/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <langapi/language_util.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set_dereference.h>

#include "goto_symex.h"
#include "goto_symex_is_constant.h"
#include "path_storage.h"

#include <algorithm>
#include <climits>
#include <iostream>

void goto_symext::apply_goto_condition(
  goto_symex_statet &current_state,
  goto_statet &jump_taken_state,
  goto_statet &jump_not_taken_state,
  const exprt &original_guard,
  const exprt &new_guard,
  const namespacet &ns)
{
  // It would be better to call try_filter_value_sets after apply_condition,
  // and pass nullptr for value sets which apply_condition successfully updated
  // already. However, try_filter_value_sets calls rename to do constant
  // propagation, and apply_condition can update the constant propagator. Since
  // apply condition will never succeed on both jump_taken_state and
  // jump_not_taken_state, it should be possible to pass a reference to an
  // unmodified goto_statet to use for renaming. But renaming needs a
  // goto_symex_statet, not just a goto_statet, and we only have access to one
  // of those. A future improvement would be to split rename into two parts:
  // one part on goto_symex_statet which is non-const and deals with
  // l2 thread reads, and one part on goto_statet which is const and could be
  // used in try_filter_value_sets.

  try_filter_value_sets(
    current_state,
    original_guard,
    jump_taken_state.value_set,
    &jump_taken_state.value_set,
    &jump_not_taken_state.value_set,
    ns);

  if(!symex_config.constant_propagation)
    return;

  jump_taken_state.apply_condition(new_guard, current_state, ns);

  // Could use not_exprt + simplify, but let's avoid paying that cost on quite
  // a hot path:
  const exprt negated_new_guard = boolean_negate(new_guard);
  jump_not_taken_state.apply_condition(negated_new_guard, current_state, ns);
}

/// Try to evaluate a simple pointer comparison.
/// \param operation: ID_equal or ID_not_equal
/// \param symbol_expr: The symbol expression in the condition
/// \param other_operand: The other expression in the condition; we only support
///   an address of expression, a typecast of an address of expression or a
///   null pointer, and return an empty optionalt in all other cases
/// \param value_set: The value-set for looking up what the symbol can point to
/// \param language_mode: The language mode
/// \param ns: A namespace
/// \return If we were able to evaluate the condition as true or false then we
///   return that, otherwise we return an empty optionalt
static optionalt<renamedt<exprt, L2>> try_evaluate_pointer_comparison(
  const irep_idt &operation,
  const symbol_exprt &symbol_expr,
  const exprt &other_operand,
  const value_sett &value_set,
  const irep_idt language_mode,
  const namespacet &ns)
{
  const constant_exprt *constant_expr =
    expr_try_dynamic_cast<constant_exprt>(other_operand);

  if(
    skip_typecast(other_operand).id() != ID_address_of &&
    (!constant_expr || !is_null_pointer(*constant_expr)))
  {
    return {};
  }

  const ssa_exprt *ssa_symbol_expr =
    expr_try_dynamic_cast<ssa_exprt>(symbol_expr);

  ssa_exprt l1_expr{*ssa_symbol_expr};
  l1_expr.remove_level_2();
  const std::vector<exprt> value_set_elements =
    value_set.get_value_set(l1_expr, ns);

  bool constant_found = false;

  for(const auto &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid ||
      is_failed_symbol(
        to_object_descriptor_expr(value_set_element).root_object()) ||
      to_object_descriptor_expr(value_set_element).offset().id() == ID_unknown)
    {
      // We can't conclude anything about the value-set
      return {};
    }

    if(!constant_found)
    {
      if(value_set_dereferencet::should_ignore_value(
           value_set_element, false, language_mode))
      {
        continue;
      }

      value_set_dereferencet::valuet value =
        value_set_dereferencet::build_reference_to(
          value_set_element, symbol_expr, ns);

      // use the simplifier to test equality as we need to skip over typecasts
      // and cannot rely on canonical representations, which would permit a
      // simple syntactic equality test
      exprt test_equal = simplify_expr(
        equal_exprt{
          typecast_exprt::conditional_cast(value.pointer, other_operand.type()),
          other_operand},
        ns);
      if(test_equal.is_true())
      {
        constant_found = true;
        // We can't break because we have to make sure we find any instances of
        // ID_unknown or ID_invalid
      }
      else if(!test_equal.is_false())
      {
        // We can't conclude anything about the value-set
        return {};
      }
    }
  }

  if(!constant_found)
  {
    // The symbol cannot possibly have the value \p other_operand because it
    // isn't in the symbol's value-set
    return operation == ID_equal ? make_renamed<L2>(false_exprt{})
                                 : make_renamed<L2>(true_exprt{});
  }
  else if(value_set_elements.size() == 1)
  {
    // The symbol must have the value \p other_operand because it is the only
    // thing in the symbol's value-set
    return operation == ID_equal ? make_renamed<L2>(true_exprt{})
                                 : make_renamed<L2>(false_exprt{});
  }
  else
  {
    return {};
  }
}

/// Check if we have a simple pointer comparison, and if so try to evaluate it.
/// \param renamed_expr: The L2-renamed expression to check
/// \param value_set: The value-set for looking up what the symbol can point to
/// \param language_mode: The language mode
/// \param ns: A namespace
/// \return If we were able to evaluate the condition as true or false then we
///   return that, otherwise we return an empty optionalt
static optionalt<renamedt<exprt, L2>> try_evaluate_pointer_comparison(
  const renamedt<exprt, L2> &renamed_expr,
  const value_sett &value_set,
  const irep_idt &language_mode,
  const namespacet &ns)
{
  const exprt &expr = renamed_expr.get();

  if(expr.id() != ID_equal && expr.id() != ID_notequal)
    return {};

  if(!can_cast_type<pointer_typet>(to_binary_expr(expr).op0().type()))
    return {};

  exprt lhs = to_binary_expr(expr).op0(), rhs = to_binary_expr(expr).op1();
  if(can_cast_expr<symbol_exprt>(rhs))
    std::swap(lhs, rhs);

  const symbol_exprt *symbol_expr_lhs =
    expr_try_dynamic_cast<symbol_exprt>(lhs);

  if(!symbol_expr_lhs)
    return {};

  if(!goto_symex_is_constantt(ns)(rhs))
    return {};

  return try_evaluate_pointer_comparison(
    expr.id(), *symbol_expr_lhs, rhs, value_set, language_mode, ns);
}

renamedt<exprt, L2> try_evaluate_pointer_comparisons(
  renamedt<exprt, L2> condition,
  const value_sett &value_set,
  const irep_idt &language_mode,
  const namespacet &ns)
{
  selectively_mutate(
    condition,
    [&value_set, &language_mode, &ns](const renamedt<exprt, L2> &expr) {
      return try_evaluate_pointer_comparison(
        expr, value_set, language_mode, ns);
    });

  return condition;
}

exprt disjunction_and_simplify_jmp(const ssa_exprt &left, const exprt &right){
  if(right == left){
    return left;
  }
  else if(right == boolean_negate(left)){
    return true_exprt();
  }
  else if(right.id() == ID_and){
    auto operands = right.operands();
    size_t j = 0;
    for(size_t i = 0; i<operands.size(); i++)
    {
      if(operands[i] != boolean_negate(left))
      {
        if(i!=j)
          operands[j] = operands[i];
        j++;
      }
    }
    if(j != operands.size()){
      if(j == 0)
        return left;
      if(j == 1)
        return disjunction({left, operands[0]});
      else{
        operands.resize(j);
        return disjunction({left, conjunction(operands)});
      }
    } else {
      return disjunction({left, right});
    }
  } else {
    return disjunction({left, right});
  }
}

// returns prev || (state_guard && new_guard)
ssa_exprt compute_and_store_jmp(const unsigned target_location_number, const unsigned call_depth, const exprt &state_guard, const exprt &new_guard, symex_target_equationt& targett, const symex_targett::sourcet &original_source)
{
  const exprt prev = targett.get_last_jmp_val(target_location_number, call_depth);
  exprt ans;
  if(prev.is_false())
  {
    PRECONDITION(!new_guard.is_false());
    if(state_guard.is_false())
      PRECONDITION(false);
    else if(state_guard.is_true()) {
      ans = new_guard;
    } else {
      if (new_guard.is_true()) {
        ans = state_guard;
      } else {
        ans = conjunction({state_guard, new_guard});
        targett.merge_irep.merged1L(ans);
      }
    }
  } else if(prev.is_true()){
    PRECONDITION(!prev.is_true());
  } else {
    if(state_guard.is_false() || new_guard.is_false()){
      PRECONDITION(!(state_guard.is_false() || new_guard.is_false()));
    } else if(state_guard.is_true()){
      if(new_guard.is_true())
        ans = new_guard;
      else {
        ans = disjunction_and_simplify_jmp(to_ssa_expr(prev), new_guard);
        if(prev == ans){
          return to_ssa_expr(prev);
        }
        targett.merge_irep.merged1L(ans);
      }
    } else {
      /*
       * TODO look for pattern: jmp_tln_cd#x || ((!jmp_tln_cd#w && other) && new_guard)
       * where w <= x && jmp_progressive_since[tln,cd] <= w (i.e., jmp_tln_cd#x and jmp_tln_cd#w refer to the same loop)
       * in that case, it becomes:
       * jmp_tln_cd#x || ((other) && new_guard)
       */

      if(new_guard.is_true())
      {
        ans = disjunction_and_simplify_jmp(to_ssa_expr(prev), state_guard);
        if(prev == ans){
          return to_ssa_expr(prev);
        }
        targett.merge_irep.merged1L(ans);
      } else {
        ans = conjunction({state_guard, new_guard});
        targett.merge_irep.merged1L(ans);
        ans = disjunction_and_simplify_jmp(to_ssa_expr(prev), ans);
        if(prev == ans){
          return to_ssa_expr(prev);
        }
        targett.merge_irep.merged1L(ans);
      }
    }
  }

  auto jmp_lhs = targett.set_last_jmp_val(target_location_number, call_depth, ans);
  //std::cout << "J " << from_expr(jmp_lhs) << " " << from_expr(ans) << "\n";
  targett.assignment(
    true_exprt(),
    jmp_lhs,
    jmp_lhs,
    jmp_lhs,
    ans,
    original_source,
    symex_targett::assignment_typet::STATE);

  return (jmp_lhs);
}

void goto_symext::symex_goto(statet &state)
{
  PRECONDITION(state.reachable);

  const goto_programt::instructiont &instruction=*state.source.pc;

  exprt new_guard = clean_expr(instruction.condition(), state, false);

  renamedt<exprt, L2> renamed_guard = state.rename(std::move(new_guard), ns);
  renamed_guard = try_evaluate_pointer_comparisons(
    std::move(renamed_guard), state.value_set, language_mode, ns);
  if(symex_config.simplify_opt)
    renamed_guard.simplify(ns);
  new_guard = renamed_guard.get();

  if(new_guard.is_false())
  {
    target.location(state.guard.as_expr(), state.source);

    // next instruction
    symex_transition(state);
    return; // nothing to do
  }

  target.goto_instruction(state.guard.as_expr(), renamed_guard, state.source);

  DATA_INVARIANT(
    !instruction.targets.empty(), "goto should have at least one target");

  // we only do deterministic gotos for now
  DATA_INVARIANT(
    instruction.targets.size() == 1, "no support for non-deterministic gotos");

  goto_programt::const_targett goto_target=
    instruction.get_target();

  const bool backward = instruction.is_backwards_goto();

  if(backward)
  {
    // is it label: goto label; or while(cond); - popular in SV-COMP
    if(
      symex_config.self_loops_to_assumptions &&
      // label: goto label; or do {} while(cond);
      (goto_target == state.source.pc ||
       // while(cond);
       (instruction.incoming_edges.size() == 1 &&
        *instruction.incoming_edges.begin() == goto_target &&
        goto_target->is_goto() && new_guard.is_true())))
    {
      // generate assume(false) or a suitable negation if this
      // instruction is a conditional goto
      exprt negated_guard = not_exprt{new_guard};
      do_simplify(negated_guard);
      log.statistics() << "replacing self-loop at "
                       << state.source.pc->source_location() << " by assume("
                       << from_expr(ns, state.source.function_id, negated_guard)
                       << ")" << messaget::eom;
      if(symex_config.unwinding_assertions)
      {
        log.warning()
          << "no unwinding assertion will be generated for self-loop at "
          << state.source.pc->source_location() << messaget::eom;
      }
      symex_assume_l2(state, negated_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    const auto loop_id =
      goto_programt::loop_id(state.source.function_id, *state.source.pc);

    unsigned &unwind = state.call_stack().top().loop_iterations[loop_id].count;
    unwind++;

    if(should_stop_unwind(state.source, state.call_stack(), unwind))
    {
      // we break the loop
      loop_bound_exceeded(state, new_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    if(new_guard.is_true())
    {
      // we continue executing the loop
      if(check_break(loop_id, unwind))
      {
        should_pause_symex = true;
      }
      symex_transition(state, goto_target, true);
      return; // nothing else to do
    }
  }

  // No point executing both branches of an unconditional goto.
  if(
    new_guard.is_true() && // We have an unconditional goto, AND
    // either there are no reachable blocks between us and the target in the
    // surrounding scope (because state.guard == true implies there is no path
    // around this GOTO instruction)
    (state.guard.is_true() ||
     // or there is another block, but we're doing path exploration so
     // we're going to skip over it for now and return to it later.
     symex_config.doing_path_exploration))
  {
    DATA_INVARIANT(
      instruction.targets.size() > 0,
      "Instruction is an unconditional goto with no target: " +
        instruction.code().pretty());
    symex_transition(state, instruction.get_target(), true);
    return;
  }

  goto_programt::const_targett new_state_pc, state_pc;
  //symex_targett::sourcet original_source=state.source;

  if(!backward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;

    // skip dead instructions
    if(new_guard.is_true())
      while(state_pc!=goto_target && !state_pc->is_target())
        ++state_pc;

    if(state_pc==goto_target)
    {
      symex_transition(state, goto_target, false);
      return; // nothing else to do
    }
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  // Normally the next instruction to execute would be state_pc and we save
  // new_state_pc for later. But if we're executing from a saved state, then
  // new_state_pc should be the state that we saved from earlier, so let's
  // execute that instead.
  if(state.has_saved_jump_target)
  {
    INVARIANT(
      new_state_pc == state.saved_target,
      "Tried to explore the other path of a branch, but the next "
      "instruction along that path is not the same as the instruction "
      "that we saved at the branch point. Saved instruction is " +
        state.saved_target->code().pretty() +
        "\nwe were intending "
        "to explore " +
        new_state_pc->code().pretty() +
        "\nthe "
        "instruction we think we saw on a previous path exploration is " +
        state_pc->code().pretty());
    goto_programt::const_targett tmp = new_state_pc;
    new_state_pc = state_pc;
    state_pc = tmp;

    log.debug() << "Resuming from jump target '" << state_pc->source_location()
                << "'" << log.eom;
  }
  else if(state.has_saved_next_instruction)
  {
    log.debug() << "Resuming from next instruction '"
                << state_pc->source_location() << "'" << log.eom;
  }
  else if(symex_config.doing_path_exploration)
  {
    // We should save both the instruction after this goto, and the target of
    // the goto.

    path_storaget::patht next_instruction(target, state);
    next_instruction.state.saved_target = state_pc;
    next_instruction.state.has_saved_next_instruction = true;

    path_storaget::patht jump_target(target, state);
    jump_target.state.saved_target = new_state_pc;
    jump_target.state.has_saved_jump_target = true;
    // `forward` tells us where the branch we're _currently_ executing is
    // pointing to; this needs to be inverted for the branch that we're saving,
    // so let its truth value for `backwards` be the same as ours for `forward`.

    log.debug() << "Saving next instruction '"
                << next_instruction.state.saved_target->source_location() << "'"
                << log.eom;
    log.debug() << "Saving jump target '"
                << jump_target.state.saved_target->source_location() << "'"
                << log.eom;
    path_storage.push(next_instruction);
    path_storage.push(jump_target);

    // It is now up to the caller of symex to decide which path to continue
    // executing. Signal to the caller that states have been pushed (therefore
    // symex has not yet completed and must be resumed), and bail out.
    should_pause_symex = true;
    return;
  }

  // put a copy of the current state into the state-queue, to be used by
  // merge_gotos when we visit new_state_pc
  framet::goto_state_listt &goto_state_list =
    state.call_stack().top().goto_state_map[new_state_pc];

  // On an unconditional GOTO we don't need our state, as it will be overwritten
  // by merge_goto. Therefore we move it onto goto_state_list instead of copying
  // as usual.
  if(new_guard.is_true())
  {
#if 0
    unsigned int target_location_number = goto_target->location_number;
    unsigned int call_depth = state.call_stack().size();
    auto old_jmpvar = target.get_last_jmp_val(target_location_number, call_depth);
    auto jmpvar = compute_and_store_jmp(
      target_location_number,
      call_depth,
      state.guard.as_expr(),
      new_guard,
      target,
      original_source);
    //if(old_jmpvar.is_false())
      state.guard.set_to(jmpvar);
#endif
    state.guard.add(new_guard);
    /*else
    {
      state.guard.set_to(conjunction({boolean_negate(old_jmpvar), jmpvar}));
      state.guard.merge_guard(target.merge_irep);
    }*/
    // The move here only moves goto_statet, the base class of goto_symex_statet
    // and not the entire thing.
    goto_state_list.emplace_back(state.source, std::move(state));

    symex_transition(state, state_pc, backward);

    state.guard = guardt(false_exprt(), guard_manager);
    state.reachable = false;
    state.id = -1;
    state.mw = -1;
    state.mbak = -1;
    state.gbak = {};
  }
  else
  {
    goto_state_list.emplace_back(state.source, state);

    symex_transition(state, state_pc, backward);

    if(!symex_config.doing_path_exploration)
    {
      // This doesn't work for --paths (single-path mode) yet, as in multi-path
      // mode we remove the implied constants at a control-flow merge, but in
      // single-path mode we don't run merge_gotos.
      auto &taken_state = backward ? state : goto_state_list.back().second;
      auto &not_taken_state = backward ? goto_state_list.back().second : state;

      apply_goto_condition(
        state,
        taken_state,
        not_taken_state,
        instruction.condition(),
        new_guard,
        ns);
    }

#if 0
    // produce new guard symbol
    exprt guard_expr;

    if(
      new_guard.id() == ID_symbol ||
      (new_guard.id() == ID_not &&
       to_not_expr(new_guard).op().id() == ID_symbol))
    {
      guard_expr=new_guard;
    }
    else
    {
      symbol_exprt guard_symbol_expr =
        symbol_exprt(statet::guard_identifier(), bool_typet());
      exprt new_rhs = boolean_negate(new_guard);

      ssa_exprt new_lhs =
        state.rename_ssa<L1>(ssa_exprt{guard_symbol_expr}, ns).get();
      new_lhs =
        state.assignment(std::move(new_lhs), new_rhs, ns, true, false).get();

      guardt guard{true_exprt{}, guard_manager};

      log.conditional_output(
        log.debug(),
        [this, &new_lhs](messaget::mstreamt &mstream) {
          mstream << "Assignment to " << new_lhs.get_identifier()
                  << " [" << pointer_offset_bits(new_lhs.type(), ns).value_or(0) << " bits]"
                  << messaget::eom;
        });

      target.assignment(
        guard.as_expr(),
        new_lhs, new_lhs, guard_symbol_expr,
        new_rhs,
        original_source,
        symex_targett::assignment_typet::GUARD);

      guard_expr = state.rename(boolean_negate(guard_symbol_expr), ns).get();
    }
    if(state.has_saved_jump_target)
    {
      if(!backward)
        state.guard.add(guard_expr);
      else
        state.guard.add(boolean_negate(guard_expr));
    }
    else
    {
      goto_statet &new_state = goto_state_list.back().second;
      if(!backward)
      {
        new_state.guard.add(guard_expr);
        state.guard.add(boolean_negate(guard_expr));
      }
      else
      {
        state.guard.add(guard_expr);
        new_state.guard.add(boolean_negate(guard_expr));
      }
      new_state.guard.merge_guard(target.merge_irep);
    }
    state.guard.merge_guard(target.merge_irep);
#endif
    //if(!state.guard.is_false())
    {
      goto_statet &new_state = goto_state_list.back().second;
      //unsigned int target_location_number = goto_target->location_number;
      //unsigned int call_depth = state.call_stack().size();
      auto do_jump = backward ? boolean_negate(new_guard) : new_guard;
      auto not_do_jump = backward ? new_guard : boolean_negate(new_guard);
      if(!backward)
        target.merge_irep.merged1L(do_jump);
      else
        target.merge_irep.merged1L(not_do_jump);
      //auto old_jmpvar = target.get_last_jmp_val(target_location_number, call_depth);

      exprt old_guard = state.guard.as_expr();
      new_state.guard.add(do_jump);
      state.guard.add(not_do_jump);

      new_state.id = ++state_id_progr;
      new_state.mw = state.id;
      new_state.mbak = state.mw;
      new_state.gbak = old_guard;
      new_state.reachable = state.reachable;

      state.mw = new_state.id;
#if 0
      auto jmpvar = compute_and_store_jmp(
        new_state_pc->location_number,
        call_depth,
        state.guard.as_expr(),
        do_jump,
        target,
        original_source);
      auto not_jmpvar = compute_and_store_jmp(
        state_pc->location_number,
        call_depth,
        state.guard.as_expr(),
        not_do_jump,
        target,
        original_source);
      {
        // state_guard = state_guard && !guard
        // new_state_guard = (new_)state_guard && guard
        //state.guard.add(boolean_negate(*jmpvar));
        //if state.guard contains a !jmpvar.ident, replace with !jmpvar
        //else, add !jmpvar
        /*if(state.guard.is_true()){
          state.guard.add(boolean_negate(jmpvar));
        } else if(is_ssa_expr(state.guard.as_expr())){
          INVARIANT(to_ssa_expr(state.guard.as_expr()).get_identifier() != jmpvar.get_identifier(), "guards are AND(jump_from, !jump_to_1, ..., !jump_to_n) where foreach i, i != from");
          state.guard.add(boolean_negate(jmpvar));
        } else if(state.guard.as_expr().id() == ID_not) {
          if(to_ssa_expr(state.guard.as_expr().operands()[0]).get_identifier() != jmpvar.get_identifier()){
            state.guard.add(boolean_negate(jmpvar));
          } else {
            INVARIANT(to_ssa_expr(state.guard.as_expr().operands()[0]).get_int(ID_L2) < jmpvar.get_int(ID_L2), "jump vars' L2 must be strictly increasing");
            to_ssa_expr(state.guard.as_expr().operands()[0]).set_level_2(jmpvar.get_int(ID_L2));
          }
        }
        else
        {
          PRECONDITION_WITH_DIAGNOSTICS(
            state.guard.as_expr().id() == ID_and,
            "must be and",
            state.guard.edit_expr().pretty(0, 0));
          bool replaced = false;
          Forall_operands(op, state.guard.edit_expr())
          {
            if(
              can_cast_expr<not_exprt>(*op) &&
              to_ssa_expr(op->operands()[0]).get_identifier() ==
                jmpvar.get_identifier())
            {
              to_ssa_expr(op->operands()[0])
                .set_level_2(jmpvar.get_int(ID_L2));
              replaced = true;
              break;
            }
          }
          if(!replaced)
            state.guard.add(boolean_negate(jmpvar));
        }
        state.guard.merge_guard(target.merge_irep);
        if (!state_pc->is_target() && state.guard.as_expr().id() == ID_and){
          auto no_jmp_var = compute_and_store_jmp(
            state_pc->location_number,
            call_depth,
            state.guard.as_expr(),
            true_exprt(),
            target,
            original_source);
          state.guard.set_to(no_jmp_var);
        }*/
        // new_state_guard = add jmpvar
        //if(old_jmpvar.is_false())
          new_state.guard.set_to(jmpvar);
          state.guard.set_to(not_jmpvar);
        /*else
        {
          new_state.guard.set_to(
            conjunction({boolean_negate(old_jmpvar), jmpvar}));
          new_state.guard.merge_guard(target.merge_irep);
        }*/
      }
#endif
    }
  }
}

void goto_symext::symex_unreachable_goto(statet &state)
{
  PRECONDITION(!state.reachable);
  // This is like symex_goto, except the state is unreachable. We try to take
  // some arbitrary choice that maintains the state guard in a reasonable state
  // in order that it simplifies properly when states are merged (in
  // merge_gotos). Note we can't try to evaluate the actual GOTO guard because
  // our constant propagator might be out of date, since we haven't been
  // executing assign instructions.

  // If the guard is already false then there's no value in this state; just
  // carry on and check the next instruction.
  if(state.guard.is_false())
  {
    symex_transition(state);
    return;
  }

  const goto_programt::instructiont &instruction = *state.source.pc;
  PRECONDITION(instruction.is_goto());
  goto_programt::const_targett goto_target = instruction.get_target();

  auto queue_unreachable_state_at_target = [&]() {
    framet::goto_state_listt &goto_state_list =
      state.call_stack().top().goto_state_map[goto_target];
    goto_statet new_state(state.guard_manager);
    new_state.guard = state.guard;
    new_state.reachable = false;
    new_state.id = state.id;
    new_state.mw = state.mw;
    new_state.mbak = state.mbak;
    new_state.gbak = state.gbak;
    goto_state_list.emplace_back(state.source, std::move(new_state));
  };

  if(instruction.condition().is_true())
  {
    if(instruction.is_backwards_goto())
    {
      // Give up trying to salvage the guard
      // (this state's guard is squashed, without queueing it at the target)
    }
    else
    {
      // Take the branch:
      queue_unreachable_state_at_target();
    }

    state.guard.add(false_exprt()); // no need to merge: it will be false
  }
  else
  {
    // Arbitrarily assume a conditional branch is not-taken, except for when
    // there's an incoming backedge, when we guess that the taken case is less
    // likely to lead to that backedge than the not-taken case.
    bool maybe_loop_head = std::any_of(
      instruction.incoming_edges.begin(),
      instruction.incoming_edges.end(),
      [&instruction](const goto_programt::const_targett predecessor) {
        return predecessor->location_number > instruction.location_number;
      });

    if(instruction.is_backwards_goto() || !maybe_loop_head)
    {
      // Assume branch not taken (fall through)
    }
    else
    {
      // Assume branch taken:
      queue_unreachable_state_at_target();
      state.guard.add(false_exprt()); // no need to merge: it will be false
    }
  }

  symex_transition(state);
}

bool goto_symext::check_break(const irep_idt &loop_id, unsigned unwind)
{
  // dummy implementation
  return false;
}

std::map<ssa_exprt, SSA_stept&> phi_function_assignments;
const bool reuse_assignments = true;

void goto_symext::merge_gotos(statet &state)
{
  framet &frame = state.call_stack().top();
  unsigned int state_target_location_number = state.source.pc->location_number;
  unsigned int call_depth = state.call_stack().size();

  // first, see if this is a target at all
  auto state_map_it = frame.goto_state_map.find(state.source.pc);
  bool did_not_create_merge_symbol = true;
  if(state_map_it == frame.goto_state_map.end())
  {
    if(state.reachable && state.guard.as_expr().has_operands())
    {
      did_not_create_merge_symbol = false;
      //std::cout<<"(1) ";
      exprt new_guard = compute_and_store_jmp(
                                state_target_location_number,
                                call_depth,
                                state.guard.as_expr(),
                                true_exprt(),
                                target,
                                state.source);
      state.guard.set_to(new_guard);
    }
    if(!target.get_last_jmp_val(state_target_location_number, call_depth).is_false())
    {
      //state.n_to_fix_guard.reset();
      target.close_jump(state_target_location_number, call_depth);
    }
    return; // nothing to do
  }

  // we need to merge
  framet::goto_state_listt &state_list = state_map_it->second;

  //std::cout << "####start#### "<<from_expr(state.guard.as_expr())<< " R " << state.reachable <<"\n";
  for(auto list_it = state_list.rbegin(); list_it != state_list.rend();
      ++list_it)
  {
    //std::cout << ".. "<<from_expr(list_it->second.guard.as_expr())<< " R " << list_it->second.reachable <<"\n";
    auto state_gbak = state.gbak;
    auto state_id = state.id;
    auto state_mw = state.mw;
    auto state_guard = state.guard.as_expr();
    auto state_mbak = state.mbak;

    if(state_id == list_it->second.mw && state_mw == list_it->second.id){
      if(list_it->second.guard.as_expr().has_operands()){
        PRECONDITION(!state.guard.as_expr().has_operands());
        list_it->second.guard.set_to(boolean_negate(state.guard.as_expr()));
      }
      if(state_id < list_it->second.id)
      {
        state_guard = *list_it->second.gbak;
        //state_id = state.id;
        state_mw = list_it->second.mbak;
        //state_mbak = state.mbak;
        //state_gbak = state.gbak;
      } else {
        state_guard = *state.gbak;
        state_id = list_it->second.id;
        state_mw = state.mbak;
        state_mbak = list_it->second.mbak;
        state_gbak = list_it->second.gbak;
      }
      //std::cout << "X " << from_expr(state_guard)<<"\n";
    }
    // non-well-nested code: if some case is not reachable, keep only the reachable case
    else if(!list_it->second.reachable){
      // do nothing
    }
    else if(!state.reachable){
      state_guard = list_it->second.guard.as_expr();
      state_id = list_it->second.id;
      state_mw = list_it->second.mw;
      state_mbak = list_it->second.mbak;
      state_gbak = list_it->second.gbak;
    }
    // non-well-nested code and both reachable: we really have to merge
    else if (did_not_create_merge_symbol){
      if(list_it->second.guard.as_expr().has_operands())
      {
        if(state.guard.as_expr().has_operands()){
          //std::cout<<"(2) ";
          exprt state1_guard = (compute_and_store_jmp(
            state_target_location_number,
            call_depth,
            state.guard.as_expr(),
            true_exprt(),
            target,
            state.source));
          //std::cout <<"2a " << to_ssa_expr(state1_guard).get_identifier().c_str() << "\n";
          auto old_list_guard = list_it->second.guard.as_expr();
          list_it->second.guard.set_to(boolean_negate(state1_guard));
          //std::cout<<"(3) ";
          state_guard = (compute_and_store_jmp(
            state_target_location_number,
            call_depth,
            old_list_guard,
            true_exprt(),
            target,
            state.source));
          //std::cout <<"2b " << to_ssa_expr(state_guard).get_identifier().c_str() << "\n";
          //std::cout <<"***\n";
        } else {
          exprt old_guard = state.guard.as_expr();
          //std::cout<<"(4) ";
          state_guard = (compute_and_store_jmp(
            state_target_location_number,
            call_depth,
            disjunction({state.guard.as_expr(), list_it->second.guard.as_expr()}),
            true_exprt(),
            target,
            state.source));
          list_it->second.guard.set_to(boolean_negate(old_guard));
          //std::cout <<"3 " << to_ssa_expr(state_guard).get_identifier().c_str() << "\n";
        }
      }
      else
      {
        //std::cout<<"(5) "<< from_expr(state_guard) << " " << from_expr(list_it->second.guard.as_expr()) << "\n";
        state_guard = (compute_and_store_jmp(
          state_target_location_number,
          call_depth,
          disjunction({state.guard.as_expr(), list_it->second.guard.as_expr()}),
          true_exprt(),
          target,
          state.source));
      }
      did_not_create_merge_symbol = false;
      //state_id = state_id; No need to create a fresh number
      state_mw = -2; //You won't be able to merge anymore
      state_mbak = -2; //You won't be able to merge anymore
      state_gbak.reset();
    } else {
      //std::cout<<"(6) " << from_expr(state_guard) << " " << from_expr(list_it->second.guard.as_expr()) << "\n";
      state_guard = (compute_and_store_jmp(
        state_target_location_number,
        call_depth,
        list_it->second.guard.as_expr(),
        true_exprt(),
        target,
        state.source));
      //std::cout <<"5 " << to_ssa_expr(state_guard).get_identifier().c_str() << "\n";
      //state_id = state_id; No need to create a fresh number
      state_mw = -2; //You won't be able to merge anymore
      state_mbak = -2; //You won't be able to merge anymore
      state_gbak.reset();
      if(list_it->second.guard.as_expr().has_operands())
      {
        list_it->second.guard.set_to(boolean_negate(state.guard.as_expr()));
      }
    }
    state.guard.set_to(state_guard);
    merge_goto(list_it->first, std::move(list_it->second), state);
    state.guard.set_to(state_guard);
    state.id = state_id;
    state.mw = state_mw;
    state.mbak = state_mbak;
    state.gbak = state_gbak;
  }
#if 0

  int which_guard_to_set_true = -2; //-2 : none, -1: state, oth: state_list[which_guard_to_set_true]
  if(target.open_jumps == 1 && target.is_open_jump(state_target_location_number, call_depth)){
    if(state.reachable)
      which_guard_to_set_true = -1;
    {
      int i = 0;
      for(auto &list_it : state_list)
      {
        if(list_it.second.reachable)
        {
          which_guard_to_set_true = i;
        }
        i++;
      }
    }
  }
  bool still_unreachable = true;
  optionalt<exprt> first_reachable;
  int lcnt = 0;
  for(auto list_it = state_list.begin(); list_it != state_list.end();++list_it){
    if(list_it->second.reachable){
      if(which_guard_to_set_true >=0 && lcnt == which_guard_to_set_true){
        list_it->second.guard.set_to(compute_and_store_jmp(
          state_target_location_number,
          call_depth,
          true_exprt(),
          true_exprt(),
          target,
          state.source));
      }
      else if(still_unreachable){
        still_unreachable = false;
        if(is_ssa_expr(list_it->second.guard.as_expr()) || list_it->second.guard.as_expr().is_constant())
        {
          first_reachable = list_it->second.guard.as_expr();
        } else {
          list_it->second.guard.set_to(compute_and_store_jmp(
            state_target_location_number,
            call_depth,
            list_it->second.guard.as_expr(),
            true_exprt(),
            target,
            state.source));
        }
      } else if(first_reachable.has_value()) {
        list_it->second.guard.set_to(compute_and_store_jmp(
          state_target_location_number,
          call_depth,
          disjunction({*first_reachable, list_it->second.guard.as_expr()}),
          true_exprt(),
          target,
          state.source));
        first_reachable.reset();
      } else {
        list_it->second.guard.set_to(compute_and_store_jmp(
          state_target_location_number,
          call_depth,
          list_it->second.guard.as_expr(),
          true_exprt(),
          target,
          state.source));
      }
    }
    lcnt++;
  }
  if(state.reachable){
    if(which_guard_to_set_true ==-1){
      state.guard.set_to(compute_and_store_jmp(
        state_target_location_number,
        call_depth,
        true_exprt(),
        true_exprt(),
        target,
        state.source));
    }
    else if(still_unreachable){
      still_unreachable = false;
      //first_reachable = state.guard.as_expr();
      if(is_ssa_expr(state.guard.as_expr()) || state.guard.as_expr().is_constant())
      {
      } else {
        state.guard.set_to(compute_and_store_jmp(
          state_target_location_number,
          call_depth,
          state.guard.as_expr(),
          true_exprt(),
          target,
          state.source));
      }
    } else if(first_reachable.has_value()) {
      state.guard.set_to(compute_and_store_jmp(
        state_target_location_number,
        call_depth,
        disjunction({*first_reachable, state.guard.as_expr()}),
        true_exprt(),
        target,
        state.source));
      first_reachable.reset();
    } else {
      state.guard.set_to(compute_and_store_jmp(
        state_target_location_number,
        call_depth,
        state.guard.as_expr(),
        true_exprt(),
        target,
        state.source));
    }
  }
  for(auto list_it = state_list.rbegin(); list_it != state_list.rend();
      ++list_it)
  {
    merge_goto(list_it->first, std::move(list_it->second), state);
  }
#endif
  if(state.reachable && !is_ssa_expr(state.guard.as_expr()) && !state.guard.is_true())
  {
    did_not_create_merge_symbol = false;
    //std::cout<<"(7) ";
    exprt new_guard = compute_and_store_jmp(
      state_target_location_number,
      call_depth,
      state.guard.as_expr(),
      true_exprt(),
      target,
      state.source);
    //std::cout <<"6 " << from_expr(state.guard.as_expr()) << " -> " << to_ssa_expr(new_guard).get_identifier().c_str() << "\n";
    state.guard.set_to(new_guard);
  }
  //state.n_to_fix_guard.reset();
  if(reuse_assignments)
    phi_function_assignments.clear();

  //std::cout <<"-> " << from_expr(state.guard.as_expr()) << " R " << state.reachable <<"\n";

  //std::cout << "####end####\n";
  INVARIANT_WITH_DIAGNOSTICS(!state.reachable || state.guard.is_true() || is_ssa_expr(state.guard.as_expr()), "Guard not ok", state.guard.as_expr().pretty(0,0));

  // clean up to save some memory
  frame.goto_state_map.erase(state_map_it);
  target.close_jump(state_target_location_number, call_depth);
}

static guardt merge_state_guards(
  goto_statet &goto_state,
  goto_symex_statet &state,
  merge_irept &merge_irep)
{
  // adjust guard, even using guards from unreachable states. This helps to
  // shrink the state guard if the incoming edge is from a path that was
  // truncated by config.unwind, config.depth or an assume-false instruction.

  // Note when an unreachable state contributes its guard, merging it in is
  // optional, since the formula already implies the unreachable guard is
  // impossible. Therefore we only integrate it when to do so simplifies the
  // state guard.

  // This function can trash either state's guards, since goto_state is dying
  // and state's guard will shortly be overwritten.

  if(
    (goto_state.reachable && state.reachable) ||
    state.guard.disjunction_may_simplify(goto_state.guard))
  {
    state.guard |= goto_state.guard;
    state.guard.merge_guard(merge_irep);
    return std::move(state.guard);
  }
  else if(!state.reachable && goto_state.reachable)
  {
    return std::move(goto_state.guard);
  }
  else
  {
    return std::move(state.guard);
  }
}

void goto_symext::fix_guard(uint guard_to_edit, bool isand, bool sign, const ssa_exprt& guard_to_add){
  //is_and == true ? guard_to_edit == `guard_to_edit old expr` && sign*guard_to_add
  //is_and == false ? guard_to_edit == `guard_to_edit old expr` || sign*guard_to_add
  // normal form: (`guard_text` && s1*g1 && s2*g2 && ... && sm*gm) || sm+1*gm+1 || ... || sn*gn

  if(target.guard_assignments.count(guard_to_edit))
  {
    // skip closed jumps
    SSA_stept &assn_step =
      target.guard_assignments.find(guard_to_edit)->second;
    exprt signed_guard_to_add;
    if(sign)
      signed_guard_to_add = guard_to_add;
    else
    {
      signed_guard_to_add = not_exprt(guard_to_add);
      target.merge_irep.merged1L(signed_guard_to_add);
    }
    if(isand)
    {
      if(can_cast_expr<and_exprt>(assn_step.ssa_rhs))
      {
        assn_step.ssa_rhs.operands().push_back(signed_guard_to_add);
      }
      else if(
        can_cast_expr<or_exprt>(assn_step.ssa_rhs) &&
        can_cast_expr<and_exprt>(assn_step.ssa_rhs.operands()[0]))
      {
        assn_step.ssa_rhs.operands()[0].operands().push_back(
          signed_guard_to_add);
        target.merge_irep.merged1L(assn_step.ssa_rhs.operands()[0]);
      }
      else
      {
        assn_step.ssa_rhs = and_exprt(assn_step.ssa_rhs, signed_guard_to_add);
      }
      target.merge_irep.merged1L(assn_step.ssa_rhs);
      to_equal_expr(assn_step.cond_expr).op1() = assn_step.ssa_rhs;
      target.merge_irep.merged1L(assn_step.cond_expr);
    }
    else
    {
      if(can_cast_expr<or_exprt>(assn_step.ssa_rhs))
      {
        assn_step.ssa_rhs.operands().push_back(signed_guard_to_add);
      }
      else
      {
        assn_step.ssa_rhs = or_exprt(assn_step.ssa_rhs, signed_guard_to_add);
      }
      target.merge_irep.merged1L(assn_step.ssa_rhs);
      to_equal_expr(assn_step.cond_expr).op1() = assn_step.ssa_rhs;
      target.merge_irep.merged1L(assn_step.cond_expr);
    }
  } /*else {
    INVARIANT(false, "already closed jump");
  }*/
}

void check_lt(const exprt& e1, const exprt& e2){
  if(is_ssa_expr(e1) && is_ssa_expr(e2)){
    //INVARIANT(e1 < e2, "ordered insertion");
  } else if(is_ssa_expr(e1)) {
    check_lt(e1, to_not_expr(e2).op());
  } else if(is_ssa_expr(e2)) {
    check_lt(to_not_expr(e1).op(), e2);
  } else {
    check_lt(to_not_expr(e1).op(), to_not_expr(e2).op());
  }
}

inline uint get_guard_l2(const exprt& e){
  if(is_ssa_expr(e))
    return (uint)e.get_int(ID_L2);
  else
    return (uint)(to_not_expr(e).op().get_int(ID_L2));
}

inline uint get_guard_l2(std::vector<exprt>::iterator eitr, const bool valid_check = true){
  if(!valid_check)
    return UINT_MAX;
  else
    return get_guard_l2(*eitr);
}

guardt goto_symext::merge_guards(goto_statet &goto_state, goto_symex_statet &state){
  //TODO handle the case when some state is unreachable
  if(goto_state.guard.is_true())
    return std::move(goto_state.guard);
  if(state.guard.is_true())
    return std::move(state.guard);
  if(!state.reachable && state.guard.is_false())
    return std::move(goto_state.guard);
  if(!goto_state.reachable && goto_state.guard.is_false())
    return std::move(state.guard);

  //both guards are sorted
  if(!can_cast_expr<and_exprt>(state.guard.edit_expr()) && !can_cast_expr<and_exprt>(goto_state.guard.edit_expr())){
    //they must be `g` and `!g`. Merge point without any jumps open
    if(can_cast_expr<not_exprt>(goto_state.guard.edit_expr())){
      PRECONDITION(goto_state.guard.edit_expr().operands()[0] == state.guard.edit_expr());
    } else {
      PRECONDITION(can_cast_expr<not_exprt>(state.guard.edit_expr()));
      PRECONDITION(state.guard.edit_expr().operands()[0] == goto_state.guard.edit_expr());
    }
    target.guard_assignments.erase(get_guard_l2(state.guard.edit_expr()));
    state.guard.set_to_and({});
    return std::move(state.guard);
  }

  optionalt<ssa_exprt> merging_guard;
  bool merging_guard_sign = false;

  if(!can_cast_expr<and_exprt>(state.guard.edit_expr())){
    merging_guard_sign = is_ssa_expr(state.guard.edit_expr());
    auto merging_guard_in_GS = boolean_negate(state.guard.edit_expr());
    if(merging_guard_sign)
      merging_guard = to_ssa_expr(state.guard.edit_expr());
    else
      merging_guard = to_ssa_expr(merging_guard_in_GS);
    bool deleted = false;
    auto &operands = goto_state.guard.edit_expr().operands();

    auto op_itr = operands.begin();
    while(op_itr != operands.end()){
      if(*op_itr == merging_guard_in_GS){
        // remove it
        PRECONDITION(!deleted);
        deleted = true;
        op_itr = operands.erase(op_itr);
      } else {
        // mark the guard
        bool si = is_ssa_expr(*op_itr);
        if(si){
          fix_guard(get_guard_l2(*op_itr), false, !merging_guard_sign, *merging_guard);
        } else {
          fix_guard(get_guard_l2(*op_itr), true, merging_guard_sign, *merging_guard);
        }
        // keep it in the final expression
        auto prev = op_itr;
        op_itr++;
        if(op_itr != operands.end())
          check_lt(*prev, *op_itr);
      }
    }
    PRECONDITION(deleted);
    if(operands.size() == 1){
      goto_state.guard.set_to(operands[0]);
    } else {
      state.guard.set_to_and(operands);
      target.merge_irep.merged1L(goto_state.guard.edit_expr());
    }
    // mark merging_guard as closed
    target.guard_assignments.erase(get_guard_l2(*merging_guard));
    return std::move(goto_state.guard);
  }

  if(!can_cast_expr<and_exprt>(goto_state.guard.edit_expr())){
    merging_guard_sign = is_ssa_expr(goto_state.guard.edit_expr());
    auto merging_guard_in_S = boolean_negate(goto_state.guard.edit_expr());
    if(merging_guard_sign)
      merging_guard = to_ssa_expr(goto_state.guard.edit_expr());
    else
      merging_guard = to_ssa_expr(merging_guard_in_S);
    bool deleted = false;
    auto &operands = state.guard.edit_expr().operands();

    auto op_itr = operands.begin();
    while(op_itr != operands.end()){
      if(*op_itr == merging_guard_in_S){
        // remove it
        PRECONDITION(!deleted);
        deleted = true;
        op_itr = operands.erase(op_itr);
      } else {
        // mark the guard
        bool si = is_ssa_expr(*op_itr);
        if(si){
          fix_guard(get_guard_l2(*op_itr), false, merging_guard_sign, *merging_guard);
        } else {
          fix_guard(get_guard_l2(*op_itr), true, !merging_guard_sign, *merging_guard);
        }
        // keep it in the final expression
        auto prev = op_itr;
        op_itr++;
        if(op_itr != operands.end())
          check_lt(*prev, *op_itr);
      }
    }
    PRECONDITION(deleted);
    if(operands.size() == 1){
      state.guard.set_to(operands[0]);
    } else {
      state.guard.set_to_and(operands);
      target.merge_irep.merged1L(state.guard.edit_expr());
    }
    target.guard_assignments.erase(get_guard_l2(*merging_guard));
    return std::move(state.guard);
  }

  auto &operands_goto_state = goto_state.guard.edit_expr().operands();
  auto op_goto_state = operands_goto_state.begin();
  auto &operands_state = state.guard.edit_expr().operands();
  auto op_state = operands_state.begin();
  std::vector<exprt> answer;
  std::vector<bool> in_goto_state;
  std::vector<bool> in_state;

  //bool has_goto_state = true, has_state = true;

  for(size_t i=0; i<operands_goto_state.size()-1; i++)
    check_lt(operands_goto_state[i], operands_goto_state[i+1]);
  for(size_t i=0; i<operands_state.size()-1; i++)
    check_lt(operands_state[i], operands_state[i+1]);

  uint guardGS_l2 = get_guard_l2(op_goto_state, op_goto_state != operands_goto_state.end());
  uint guardS_l2 = get_guard_l2(op_state, op_state != operands_state.end());

  while(guardGS_l2 != UINT_MAX || guardS_l2 != UINT_MAX){
    //bool signGS = !has_goto_state || is_ssa_expr(*op_goto_state);
    //bool signS = !has_state || is_ssa_expr(*op_state);
    //auto guardGS = has_goto_state?(signGS ? *op_goto_state : to_not_expr(*op_goto_state).op()):nil_exprt();
    //auto guardS = has_state?(signS ? *op_state : to_not_expr(*op_state).op()):nil_exprt();
    if(guardGS_l2 < guardS_l2){
      // *guardGS only in the goto_state
      if(target.guard_assignments.count(guardGS_l2)){
        // open jump, keep
        answer.push_back(*op_goto_state);
        if(answer.size()>1)
          check_lt(*(answer.end()-2), answer.back());
        in_goto_state.push_back(true);
        in_state.push_back(false);
      } //else closed jump, it will be indirectly encoded in the final or.
      op_goto_state++; guardGS_l2 = get_guard_l2(op_goto_state, op_goto_state != operands_goto_state.end());
    }
    else if(guardS_l2 < guardGS_l2){
      // *guardS only in the state
      if(target.guard_assignments.count(guardS_l2)){
        // open jump, keep
        answer.push_back(*op_state);
        if(answer.size()>1)
          check_lt(*(answer.end()-2), answer.back());
        in_goto_state.push_back(false);
        in_state.push_back(true);
      } //else closed jump, it will be indirectly encoded in the final or.
      op_state++; guardS_l2 = get_guard_l2(op_state, op_state != operands_state.end());
    } else {
      // it is not closed: otherwise, it would not appear in both guards
      PRECONDITION(target.guard_assignments.count(guardS_l2));
      // in both guards
      if(*op_goto_state == *op_state){
        // same sign, it's a common path
        answer.push_back(*op_state);
        if(answer.size()>1)
          check_lt(*(answer.end()-2), answer.back());
        in_goto_state.push_back(true);
        in_state.push_back(true);
      } else {
        // that's a merging point! there's one and only one
        INVARIANT(!merging_guard, "there's only one merging guard");
        merging_guard_sign = is_ssa_expr(*op_goto_state);
        merging_guard = to_ssa_expr(merging_guard_sign?*op_goto_state:*op_state);
      }
      op_state++; guardS_l2 = get_guard_l2(op_state, op_state != operands_state.end());
      op_goto_state++; guardGS_l2 = get_guard_l2(op_goto_state, op_goto_state != operands_goto_state.end());
    }
  }
  INVARIANT(merging_guard, "there's one merging guard");
  for(size_t i=0; i<answer.size(); i++){
    if(in_goto_state[i] && in_state[i]){
      //common branch, no updates. It's an open jump
    } else if(in_goto_state[i]){
      if(is_ssa_expr(answer[i]))
      { //si == true
        fix_guard(get_guard_l2(answer[i]), false, !merging_guard_sign, *merging_guard);
      } else { // si == false
        fix_guard(get_guard_l2(answer[i]), true, merging_guard_sign, *merging_guard);
      }
    } else { //if(in_state[i])
      if(is_ssa_expr(answer[i]))
      { //sj == true
        fix_guard(get_guard_l2(answer[i]), false, merging_guard_sign, *merging_guard);
      } else { // sj == false
        fix_guard(get_guard_l2(answer[i]), true, !merging_guard_sign, *merging_guard);
      }
    }
  }
  // mark merging_guard as closed
  target.guard_assignments.erase(get_guard_l2(*merging_guard));
  state.guard.set_to_and(answer);
  target.merge_irep.merged1L(state.guard.edit_expr());
  return std::move(state.guard);
}

void goto_symext::merge_goto(
  const symex_targett::sourcet &,
  goto_statet &&goto_state,
  statet &state)
{
  // check atomic section
  if(state.atomic_section_id != goto_state.atomic_section_id)
    throw incorrect_goto_program_exceptiont(
      "atomic sections differ across branches",
      state.source.pc->source_location());

  // Merge guards. Don't write this to `state` yet because we might move
  // goto_state over it below.
#if 0
  guardt new_guard = merge_state_guards(goto_state, state, target.merge_irep);
#else
  /*static int cntr;
  std::cerr << "*************** Merge "<<cntr<<" begin:\n";
  std::cerr << "goto_state\n" << goto_state.guard.edit_expr().pretty(0,0) << "\n\n";
  std::cerr << "state\n" << state.guard.edit_expr().pretty(0,0) << "\n\n";*/
  //guardt new_guard = merge_guards(goto_state, state);
  /*std::cerr << "new_guard\n" << new_guard.edit_expr().pretty(0,0) << "\n\n";
  std::cerr << "*************** Merge end\n";
  cntr++;*/
#endif


  // Merge constant propagator, value-set etc. only if the incoming state is
  // reachable:
  if(goto_state.reachable)
  {
    if(!state.reachable)
    {
      // Important to note that we're moving into our base class here.
      // Note this overwrites state.guard, but we restore it below.
      static_cast<goto_statet &>(state) = std::move(goto_state);
    }
    else
    {
      // do SSA phi functions
      phi_function(goto_state, state);

      // merge value sets
      state.value_set.make_union(goto_state.value_set);

      // adjust depth
      state.depth = std::min(state.depth, goto_state.depth);
    }
  }

  // Save the new state guard
  //state.guard = std::move(new_guard);
  //state.guard.set_to(target.get_last_jmp_val(state.source.pc->location_number));
}

/// Helper function for \c phi_function which merges the names of an identifier
/// for two different states.
/// \param goto_state: first state
/// \param [in, out] dest_state: second state
/// \param ns: namespace
/// \param diff_guard: difference between the guards of the two states
/// \param [out] log: logger for debug messages
/// \param do_simplify_phi: should the right-hand-side of the assignment that is
///   added to the target be simplified
/// \param [out] target: equation that will receive the resulting assignment
/// \param dirty: dirty-object analysis
/// \param ssa: SSA expression to merge
/// \param goto_count: current level 2 count in \p goto_state of
///   \p l1_identifier
/// \param dest_count: level 2 count in \p dest_state of \p l1_identifier
static void merge_names(
  const goto_statet &goto_state,
  goto_symext::statet &dest_state,
  const namespacet &ns,
  const exprt &diff_guard,
  messaget &log,
  const bool do_simplify_phi,
  symex_target_equationt &target,
  const incremental_dirtyt &dirty,
  const ssa_exprt &ssa,
  const unsigned goto_count,
  const unsigned dest_count,
  const optionalt<int> extract_phi)
{
  const irep_idt l1_identifier = ssa.get_identifier();
  const irep_idt &obj_identifier = ssa.get_object_name();

  if(obj_identifier == goto_symext::statet::guard_identifier())
    return; // just a guard, don't bother

  if(as_string(obj_identifier).find("\\jmp_", 0) == 0)
    return; // just a jmp, don't bother

  if(goto_count == dest_count)
    return; // not at all changed

  // changed - but only on a branch that is now dead, and the other branch is
  // uninitialized/invalid
  if(
    (!dest_state.reachable && goto_count == 0) ||
    (!goto_state.reachable && dest_count == 0))
  {
    return;
  }

  // field sensitivity: only merge on individual fields
  if(dest_state.field_sensitivity.is_divisible(ssa, true))
    return;

  // shared variables are renamed on every access anyway, we don't need to
  // merge anything
  const symbolt &symbol = ns.lookup(obj_identifier);

  // shared?
  if(
    dest_state.atomic_section_id == 0 && dest_state.threads.size() >= 2 &&
    (symbol.is_shared() || dirty(symbol.name)))
  {
    return; // no phi nodes for shared stuff
  }

  // don't merge (thread-)locals across different threads, which
  // may have been introduced by symex_start_thread (and will
  // only later be removed from level2.current_names by pop_frame
  // once the thread is executed)
  const irep_idt level_0 = ssa.get_level_0();
  if(
    !level_0.empty() &&
    level_0 != std::to_string(dest_state.source.thread_nr) && dest_count != 0)
  {
    return;
  }

  exprt goto_state_rhs = ssa, dest_state_rhs = ssa, dest_state_guard;

  bool goto_state_cp;
  {
    const auto p_it = goto_state.propagation.find(l1_identifier);

    goto_state_cp = p_it.has_value();

    if(goto_state_cp)
      goto_state_rhs = *p_it;
    else
      to_ssa_expr(goto_state_rhs).set_level_2(goto_count);
  }

  bool has_older_phi_function = false;

  {
    const auto p_it = dest_state.propagation.find(l1_identifier);

    if(p_it.has_value())
    {
      dest_state_rhs = *p_it;
      /*if(!goto_state_cp || dest_state_rhs != goto_state_rhs)
        dest_state.propagation.erase(l1_identifier);*/
      if(reuse_assignments && phi_function_assignments.count(ssa))
      {
        dest_state_guard = phi_function_assignments.find(ssa)->second.guard;
        has_older_phi_function = true;
      }
    } else if(reuse_assignments && phi_function_assignments.count(ssa)){
      dest_state_rhs = phi_function_assignments.find(ssa)->second.ssa_rhs;
      dest_state_guard = phi_function_assignments.find(ssa)->second.guard;
      has_older_phi_function = true;
    }
    else
      to_ssa_expr(dest_state_rhs).set_level_2(dest_count);
  }

  exprt rhs;

  // Don't add a conditional to the assignment when:
  //  1. Either guard is false, so we can't follow that branch.
  //  2. Either identifier is of generation zero, and so hasn't been
  //     initialized and therefore an invalid target.

  // These rules only apply to dynamic objects and locals.
  if(!dest_state.reachable)
    rhs = goto_state_rhs;
  else if(!goto_state.reachable)
    rhs = dest_state_rhs;
  else if(goto_count == 0)
    rhs = dest_state_rhs;
  else if(dest_count == 0)
    rhs = goto_state_rhs;
  else
  {
    if(extract_phi && ssa.type().get_string(ID_C_typedef) != "__cs_mutex_t")
    {
      const size_t abs_width = *extract_phi;
      const auto lb = from_integer(0, unsignedbv_typet{1});
      const auto ab_type = unsignedbv_typet{abs_width};
      if(
        const auto ibt =
          type_try_dynamic_cast<integer_bitvector_typet>(ssa.type()))
      {
        const auto lhs_name = as_string(ssa.get_original_name());
        if(
          ibt->get_width() > abs_width &&
          lhs_name.find("_cs_") == std::string::npos &&
          lhs_name.find("__CPROVER_") != 0)
        {
          const auto zero = constant_exprt{"0", ssa.type()};
          goto_state_rhs = make_byte_update(
            zero, lb, make_byte_extract(goto_state_rhs, lb, ab_type));
          dest_state_rhs = make_byte_update(
            zero, lb, make_byte_extract(dest_state_rhs, lb, ab_type));
          //log.warning() << "ABSTR: " << lhs_name << messaget::eom;
        }
      }
    }
    if(has_older_phi_function)
    {
      if(do_simplify_phi)
        simplify(goto_state_rhs, ns);
      rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_state_rhs);
      if(diff_guard.is_true()){
        rhs = goto_state_rhs;
      } else if(diff_guard.is_false()) {
        rhs = dest_state_rhs;
      }
      else if(auto dest_if = expr_try_dynamic_cast<if_exprt>(dest_state_rhs)){
        if(dest_if->cond() == diff_guard) {
          rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_if->false_case());
        } /*else if(dest_if->true_case() == goto_state_rhs){
          rhs = if_exprt(disjunction({diff_guard, dest_if->cond()}), goto_state_rhs, dest_if->false_case());
        }*/ else if(dest_if->false_case() == goto_state_rhs){
          rhs = dest_state_rhs;
        } else {
          rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_state_rhs);
        }
      }
      else {
        //rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_state_rhs);
        rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_state_rhs);
      }
      if(do_simplify_phi)
        simplify(rhs, ns);
    } else
    {
      rhs = if_exprt(diff_guard /*.as_expr()*/, goto_state_rhs, dest_state_rhs);
      if(do_simplify_phi)
        simplify(rhs, ns);
    }
  }


  if(has_older_phi_function){
    dest_state.record_events.push(false);
    const ssa_exprt new_lhs =
      dest_state.assignment(ssa, rhs, ns, true, true).get();
    dest_state.record_events.pop();

    auto step_ref = phi_function_assignments.find(ssa);
    step_ref->second.ssa_rhs = rhs;
    step_ref->second.ssa_lhs = new_lhs;
    step_ref->second.ssa_full_lhs = new_lhs;
    step_ref->second.original_full_lhs = new_lhs.get_original_expr();
    step_ref->second.cond_expr = equal_exprt(new_lhs, rhs);
    target.SSA_steps.back().guard = dest_state.guard.as_expr();
    target.merge_irep.merged1L(step_ref->second.cond_expr);
  } else
  {
    dest_state.record_events.push(false);
    const ssa_exprt new_lhs =
      dest_state.assignment(ssa, rhs, ns, true, true).get();
    dest_state.record_events.pop();

    log.conditional_output(
      log.debug(),
      [ns, &new_lhs](messaget::mstreamt &mstream)
      {
        mstream << "Assignment to " << new_lhs.get_identifier() << " ["
                << pointer_offset_bits(new_lhs.type(), ns).value_or(0)
                << " bits]" << messaget::eom;
      });

    target.assignment(
      true_exprt(),
      new_lhs,
      new_lhs,
      new_lhs.get_original_expr(),
      rhs,
      dest_state.source,
      symex_targett::assignment_typet::PHI);
    target.SSA_steps.back().guard = dest_state.guard.as_expr();
    if(reuse_assignments)
      phi_function_assignments.emplace(ssa, target.SSA_steps.back());
  }
}

void goto_symext::phi_function(
  const goto_statet &goto_state,
  statet &dest_state)
{
  if(
    goto_state.get_level2().current_names.empty() &&
    dest_state.get_level2().current_names.empty())
    return;

  /*guardt diff_guard = goto_state.guard;
  // this gets the diff between the guards
  diff_guard -= dest_state.guard;*/
  exprt diff_guard;
  if(can_cast_expr<and_exprt>(goto_state.guard.as_expr())){
    diff_guard = goto_state.guard.as_expr().operands().back();
  } else {
    diff_guard = goto_state.guard.as_expr();
  }
  INVARIANT_WITH_DIAGNOSTICS(is_ssa_expr(diff_guard) || is_ssa_expr(boolean_negate(diff_guard)), "Precondition", diff_guard.pretty());

  symex_renaming_levelt::delta_viewt delta_view;
  goto_state.get_level2().current_names.get_delta_view(
    dest_state.get_level2().current_names, delta_view, false);

  for(const auto &delta_item : delta_view)
  {
    const ssa_exprt &ssa = delta_item.m.first;
    unsigned goto_count = delta_item.m.second;
    unsigned dest_count = !delta_item.is_in_both_maps()
                            ? 0
                            : delta_item.get_other_map_value().second;

    merge_names(
      goto_state,
      dest_state,
      ns,
      diff_guard,
      log,
      symex_config.simplify_phi,
      target,
      path_storage.dirty,
      ssa,
      goto_count,
      dest_count,
      extract_phi);
  }

  delta_view.clear();
  dest_state.get_level2().current_names.get_delta_view(
    goto_state.get_level2().current_names, delta_view, false);

  for(const auto &delta_item : delta_view)
  {
    if(delta_item.is_in_both_maps())
      continue;

    const ssa_exprt &ssa = delta_item.m.first;
    unsigned goto_count = 0;
    unsigned dest_count = delta_item.m.second;

    merge_names(
      goto_state,
      dest_state,
      ns,
      diff_guard,
      log,
      symex_config.simplify_phi,
      target,
      path_storage.dirty,
      ssa,
      goto_count,
      dest_count,
      extract_phi);
  }
}

void goto_symext::loop_bound_exceeded(
  statet &state,
  const exprt &guard)
{
  const unsigned loop_number=state.source.pc->loop_number;

  exprt negated_cond;

  if(guard.is_true())
    negated_cond=false_exprt();
  else
    negated_cond=not_exprt(guard);

  if(symex_config.unwinding_assertions)
  {
    // Generate VCC for unwinding assertion.
    vcc(
      negated_cond,
      "unwinding assertion loop " + std::to_string(loop_number),
      state);
  }

  if(!symex_config.partial_loops)
  {
    // generate unwinding assumption, unless we permit partial loops
    symex_assume_l2(state, negated_cond);
  }
}

bool goto_symext::should_stop_unwind(
  const symex_targett::sourcet &,
  const call_stackt &,
  unsigned)
{
  // by default, we keep going
  return false;
}
