//
// Created by giulio on 25/05/23.
//

#include <util/abstraction.h>

#include "bitvector_expr.h"
#include "bitvector_types.h"
#include "c_types.h"
#include "cprover_prefix.h"

void produce_nonabs(exprt &e, symex_target_equationt &targetEquation){
  if((*targetEquation.produce_nonabs)[e].has_value()){
    return;
  }
  if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    (*targetEquation.produce_nonabs)[e] = !is_abstractable_name(as_string(ssa->get_original_name()));
  } else if (e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult ||
          e.id() == ID_div || e.id() == ID_shl || e.id() == ID_shr ||
          e.id() == ID_lshr || e.id() == ID_ashr || e.id() == ID_rol || e.id() == ID_ror ||
          e.id() == ID_array || e.id() == ID_array_of || e.id() == ID_bitreverse ||
          e.id() == ID_bitand || e.id()==ID_bitor || e.id()==ID_bitxor ||
          e.id() == ID_bitnand || e.id() == ID_bitnor || e.id() == ID_bitxnor ||
          e.id() == ID_bitnot || e.id() == ID_bswap || e.id() == ID_abs ||
          e.id() == ID_byte_extract_little_endian || e.id() == ID_byte_extract_big_endian ||
          e.id() == ID_extractbit || e.id() == ID_extractbits ||
          e.id() == ID_byte_update_little_endian || e.id() == ID_byte_update_big_endian ||
          e.id() == ID_complex || e.id() == ID_complex_imag || e.id() == ID_complex_real ||
          e.id() == ID_concatenation || e.id() == ID_cond ||
          e.id() == ID_floatbv_mod || e.id() == ID_floatbv_rem || e.id() == ID_floatbv_plus ||
          e.id() == ID_floatbv_minus || e.id() == ID_floatbv_mult || e.id() == ID_floatbv_div ||
          e.id() == ID_let || e.id() == ID_member || e.id() == ID_onehot ||
          e.id() == ID_onehot0 || e.id() == ID_overflow_minus || e.id() == ID_overflow_plus ||
          e.id() == ID_overflow_mult  || e.id() == ID_overflow_unary_minus || e.id() == ID_overflow_shl ||
          e.id() == ID_overflow_result_minus || e.id() == ID_overflow_result_plus ||
          e.id() == ID_overflow_result_mult || e.id() == ID_overflow_result_unary_minus ||
          e.id() == ID_overflow_result_shl || e.id() == ID_power ||
          e.id() == ID_reduction_or || e.id() == ID_reduction_and ||
          e.id() == ID_reduction_nand || e.id() == ID_reduction_nor ||
          e.id() == ID_reduction_xor || e.id() == ID_reduction_xnor ||
          e.id() == ID_struct || e.id() == ID_union || e.id() == ID_update ||
          e.id() == ID_vector || e.id() == ID_with || e.id() == ID_ge ||
          e.id() == ID_le || e.id() == ID_gt ||
          e.id() == ID_lt || e.id() == ID_equal || e.id() == ID_notequal ||
          e.id() == ID_ieee_float_equal || e.id() == ID_ieee_float_notequal ||
          e.id() == ID_forall || e.id() == ID_exists || e.id() == ID_not ||
          e.id() == ID_implies || e.id() == ID_address_of || e.id() == ID_and ||
          e.id() == ID_or || e.id() == ID_nand || e.id() == ID_nor ||
          e.id() == ID_xor || e.id() == ID_pointer_object || e.id() == ID_pointer_offset) {
    (*targetEquation.produce_nonabs)[e] = true;
    Forall_operands(op, e){
      produce_nonabs(e.operands()[0], targetEquation);
    }
  } else if(e.id() == ID_case){
    // produce nonabs for every op[e'] (e>0 AND e' is even) AND this op produce nonabs
    (*targetEquation.produce_nonabs)[e] = true;
    for(std::vector<exprt>::size_type i=2; i<e.operands().size(); i+=2){
      produce_nonabs(e.operands()[i], targetEquation);
    }
  } else if (e.id() == ID_constant){
    (*targetEquation.produce_nonabs)[e] = true;
  } else if (e.id() == ID_nondet_symbol){
    (*targetEquation.produce_nonabs)[e] = false;
  } else if(const auto ifexp = expr_try_dynamic_cast<if_exprt>(e)){
    // produce nonabs for then and else AND this op has produce nonabs
    (*targetEquation.produce_nonabs)[e] = true;
    produce_nonabs(ifexp->true_case(), targetEquation);
    produce_nonabs(ifexp->false_case(), targetEquation);
  } else if(const auto index = expr_try_dynamic_cast<index_exprt>(e)){
    (*targetEquation.produce_nonabs)[e] = true;
    produce_nonabs(index->index(), targetEquation);
  } else if(const auto repl = expr_try_dynamic_cast<replication_exprt>(e)){
    (*targetEquation.produce_nonabs)[e] = true;
    produce_nonabs(repl->op(), targetEquation);
  } else if(const auto cast = expr_try_dynamic_cast<typecast_exprt>(e)){
    (*targetEquation.produce_nonabs)[e] = true;
    produce_nonabs(cast->op(), targetEquation);
  } else {
    UNREACHABLE;
  }
}

/* unknown expressions:
 * ID_constraint_select_one
 */
bool set_if_abs_forbidden(exprt &e, symex_target_equationt &targetEquation){
  if((*targetEquation.is_abs_forbidden)[e].has_value()){
    return *((*targetEquation.is_abs_forbidden)[e]);
  }
  else if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    bool is_out_of_abs = !is_abstractable_name(as_string(ssa->get_original_name()));
    ((*targetEquation.is_abs_forbidden)[e]) = is_out_of_abs;
    if(is_out_of_abs)
      (*targetEquation.produce_nonabs)[e] =  true;
  } else if(e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult ||
          e.id() == ID_div || e.id() == ID_shl || e.id() == ID_shr ||
          e.id() == ID_lshr || e.id() == ID_ashr || e.id() == ID_rol || e.id() == ID_ror ||
          e.id() == ID_array || e.id() == ID_array_of || e.id() == ID_bitreverse ||
          e.id() == ID_bitand || e.id() == ID_bitor || e.id() == ID_bitxor ||
          e.id() == ID_bitnand || e.id() == ID_bitnor || e.id() == ID_bitxnor ||
          e.id() == ID_bitnot || e.id() == ID_bswap || e.id() == ID_abs ||
          e.id() == ID_byte_extract_little_endian || e.id() == ID_byte_extract_big_endian ||
          e.id() == ID_extractbit || e.id() == ID_extractbits ||
          e.id() == ID_byte_update_little_endian || e.id() == ID_byte_update_big_endian ||
          e.id() == ID_complex || e.id() == ID_complex_imag || e.id() == ID_complex_real ||
          e.id() == ID_concatenation || e.id() == ID_cond ||
          e.id() == ID_floatbv_mod || e.id() == ID_floatbv_rem || e.id() == ID_floatbv_plus ||
          e.id() == ID_floatbv_minus || e.id() == ID_floatbv_mult || e.id() == ID_floatbv_div ||
          e.id() == ID_let || e.id() == ID_member || e.id() == ID_onehot ||
          e.id() == ID_onehot0 || e.id() == ID_overflow_minus || e.id() == ID_overflow_plus ||
          e.id() == ID_overflow_mult  || e.id() == ID_overflow_unary_minus || e.id() == ID_overflow_shl ||
          e.id() == ID_overflow_result_minus || e.id() == ID_overflow_result_plus ||
          e.id() == ID_overflow_result_mult || e.id() == ID_overflow_result_unary_minus ||
          e.id() == ID_overflow_result_shl || e.id() == ID_power ||
          e.id() == ID_reduction_or || e.id() == ID_reduction_and ||
          e.id() == ID_reduction_nand || e.id() == ID_reduction_nor ||
          e.id() == ID_reduction_xor || e.id() == ID_reduction_xnor ||
          e.id() == ID_struct || e.id() == ID_union || e.id() == ID_update ||
          e.id() == ID_vector || e.id() == ID_with || e.id() == ID_address_of ||
          e.id() == ID_pointer_object || e.id() == ID_pointer_offset){
    // exists op with abs_forbidden => this op has abs_forbidden
    // exists op with abs_forbidden => produce nonabs for every op
    bool forbOp = false;
    Forall_operands(op, e){
      forbOp = set_if_abs_forbidden(*op, targetEquation) || forbOp;
    }
    ((*targetEquation.is_abs_forbidden)[e]) = forbOp;
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
      Forall_operands(op, e){
        produce_nonabs(e.operands()[0], targetEquation);
      }
    }
  } else if(e.id() == ID_ge || e.id() == ID_le || e.id() == ID_gt ||
          e.id() == ID_lt || e.id() == ID_equal || e.id() == ID_notequal ||
          e.id() == ID_ieee_float_equal || e.id() == ID_ieee_float_notequal ||
          e.id() == ID_forall || e.id() == ID_exists || e.id() == ID_not ||
          e.id() == ID_implies || e.id() == ID_and || e.id() == ID_or ||
          e.id() == ID_nand || e.id() == ID_nor || e.id() == ID_xor) {
    // NOT this op has abs_forbidden
    // exists op with abs_forbidden => produce nonabs for every op
    bool forbOp = false;
    Forall_operands(op, e){
      forbOp = set_if_abs_forbidden(*op, targetEquation) || forbOp;
    }
    ((*targetEquation.is_abs_forbidden)[e]) = false;
    (*targetEquation.produce_nonabs)[e] = true;
    if(forbOp){
      Forall_operands(op, e){
        produce_nonabs(e.operands()[0], targetEquation);
      }
    }
  } else if(e.id() == ID_case){
    // exists op[o] with abs_forbidden AND (o=0 OR o is odd) => produce nonabs for every op[o'] (o'=0 OR o' is odd)
    // exists op[e] with abs_forbidden AND e>0 AND e is even => produce nonabs for every op[e'] (e>0 AND e' is even) AND this op has abs_forbidden
    bool forbOp_o = false;
    bool forbOp_e = false;
    for(std::vector<exprt>::size_type i=0; i<e.operands().size(); i++){
      if(i == 0 || i%2 == 1){
        forbOp_o = set_if_abs_forbidden(e.operands()[i], targetEquation) || forbOp_o;
      } else {
        forbOp_e = set_if_abs_forbidden(e.operands()[i], targetEquation) || forbOp_e;
      }
    }
    ((*targetEquation.is_abs_forbidden)[e]) = forbOp_e;
    if(forbOp_e)
      (*targetEquation.produce_nonabs)[e] = true;
    for(std::vector<exprt>::size_type i=0; i<e.operands().size(); i++){
      if(i == 0 || i%2 == 1){
        if(forbOp_o)
          produce_nonabs(e.operands()[i], targetEquation);
      } else {
        if(forbOp_e)
          produce_nonabs(e.operands()[i], targetEquation);
      }
    }
  } else if (e.id() == ID_constant){
    (*targetEquation.is_abs_forbidden)[e] = false;
    (*targetEquation.produce_nonabs)[e] = false;
  } else if (e.id() == ID_nondet_symbol){
    (*targetEquation.is_abs_forbidden)[e] = true;
    (*targetEquation.produce_nonabs)[e] = false;
  } else if(const auto ifexp = expr_try_dynamic_cast<if_exprt>(e)){
    // then or else with abs_forbidden => produce nonabs for then and else AND this op has abs_forbidden
    set_if_abs_forbidden(ifexp->cond(), targetEquation);
    bool forbOp = set_if_abs_forbidden(ifexp->true_case(), targetEquation);
    forbOp = set_if_abs_forbidden(ifexp->false_case(), targetEquation) || forbOp;
    ((*targetEquation.is_abs_forbidden)[e]) =  forbOp;
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
      produce_nonabs(ifexp->true_case(), targetEquation);
      produce_nonabs(ifexp->false_case(), targetEquation);
    }
  } else if(const auto index = expr_try_dynamic_cast<index_exprt>(e)){
    // array with abs_forbidden => this op has abs_forbidden
    set_if_abs_forbidden(index->index(), targetEquation);
    bool forbOp = set_if_abs_forbidden(index->array(), targetEquation);
    ((*targetEquation.is_abs_forbidden)[e]) =  forbOp;
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
    }
  } else if(const auto repl = expr_try_dynamic_cast<replication_exprt>(e)){
    // op with abs_forbidden => this op has abs_forbidden
    bool forbOp = set_if_abs_forbidden(repl->op(), targetEquation);
    ((*targetEquation.is_abs_forbidden)[e]) = forbOp;
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
    }
  } else if(const auto cast = expr_try_dynamic_cast<typecast_exprt>(e)){
    // op with abs_forbidden => this op has abs_forbidden
    bool forbOp = set_if_abs_forbidden(cast->op(), targetEquation);
    ((*targetEquation.is_abs_forbidden)[e]) =  forbOp;
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
    }
  } else {
    UNREACHABLE;
  }
  return *((*targetEquation.is_abs_forbidden)[e]);
}

void annotate_ssa_exprs_tree(exprt &e, symex_target_equationt &targetEquation){
  if(e.is_nil())
    return ;
  bool pna = targetEquation.produce_nonabs.has_value() &&
             (*targetEquation.produce_nonabs)[e].has_value() &&
             *(*targetEquation.produce_nonabs)[e];
  bool forb = targetEquation.is_abs_forbidden.has_value() &&
              (*targetEquation.is_abs_forbidden)[e].has_value() &&
              *(*targetEquation.is_abs_forbidden)[e];
  e.set(ID_C_produce_nonabs, pna);
  e.set(ID_C_abstr_forbidden, forb);
  for(exprt &s: e.operands())
    annotate_ssa_exprs_tree(s, targetEquation);
}

void annotate_ssa_exprs_tree(symex_target_equationt &targetEquation)
{
  for(SSA_stept &step:targetEquation.SSA_steps){
    if(step.is_shared_read() || step.is_shared_write())
      annotate_ssa_exprs_tree(step.ssa_lhs, targetEquation);
    else
      annotate_ssa_exprs_tree(step.cond_expr, targetEquation);
    annotate_ssa_exprs_tree(step.guard, targetEquation);
  }
}

void apply_approx(symex_target_equationt &targetEquation)
{
  symex_target_equationt::SSA_stepst abs_steps;
  targetEquation.is_abs_forbidden = {std::map<exprt,optionalt<bool>>()};
  targetEquation.produce_nonabs = {std::map<exprt,optionalt<bool>>()};
  for(SSA_stept &step:targetEquation.SSA_steps){
    set_if_abs_forbidden(step.guard, targetEquation);
    switch(step.type)
    {
    case goto_trace_stept::typet::NONE:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ASSIGNMENT:{
      set_if_abs_forbidden(step.ssa_lhs, targetEquation);
      set_if_abs_forbidden(step.ssa_rhs, targetEquation);
      if(step.ssa_lhs.get_bool(ID_C_abstr_forbidden))
      {
        produce_nonabs(step.ssa_lhs, targetEquation);
        produce_nonabs(step.ssa_rhs, targetEquation);
      }
      abs_steps.emplace_back(step);
      break;}
    case goto_trace_stept::typet::ASSUME:
      set_if_abs_forbidden(step.cond_expr, targetEquation);
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ASSERT:
      set_if_abs_forbidden(step.cond_expr, targetEquation);
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::GOTO:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::LOCATION:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::INPUT:
      /*if(is_abstractable_name(as_string(step.io_id))){
        for(exprt& e:step.io_args)
          set_if_abs_forbidden(e, targetEquation);
      } else {
        for(exprt& e:step.io_args)
          produce_nonabs(e, targetEquation);
      }*/
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::OUTPUT:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::DECL:
      /*if(is_abstractable_name(as_string(step.io_id))){
        for(exprt& e:step.io_args)
          set_if_abs_forbidden(e, targetEquation);
      } else {
        for(exprt& e:step.io_args)
          produce_nonabs(e, targetEquation);
      }*/
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::DEAD:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::FUNCTION_CALL:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::FUNCTION_RETURN:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::CONSTRAINT:
      set_if_abs_forbidden(step.cond_expr, targetEquation);
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::SHARED_READ:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::SHARED_WRITE:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::SPAWN:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::MEMORY_BARRIER:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ATOMIC_BEGIN:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ATOMIC_END:
      abs_steps.emplace_back(step);
      break;
    default:
      UNREACHABLE;
    }
  }
  targetEquation.SSA_steps = std::move(abs_steps);
}

/*
 * this
 * - returns an expression saying whether the expression is abstract;
 * -
 * - marks +,/,-,*,>> whether they should return the overflow bit;
 * */
const exprt is_expr_abstract(exprt &e, size_t width){
  auto &ab = e.find(ID_C_abstr_expr);
  if(ab.is_not_nil()){
    return static_cast<const exprt&>(ab);
  }
  if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    if(is_abstractable_type(ssa->type(), width) && is_abstractable_name(as_string(ssa->get_original_name())))
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, is_abstractt(*ssa)));
    else
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, false_exprt()));
  } else if(e.id() == ID_abs) {
    or_exprt o = or_exprt(expr_protectedt::operandst());
    bool is_true = false;
    bool is_false = true;
    Forall_operands(op, e){
      const auto ab_op = is_expr_abstract(*op, width);
      if(ab_op.is_true())
      {
        is_true = true; is_false = false;
      }
      else if(!ab_op.is_false()){
        is_false = false;
        o.add_to_operands(ab_op);
      }
    }
    if(is_true){
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, true_exprt()));
    }
    else if(is_false){
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, false_exprt()));
    } else {
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, o));
    }
  } else if (e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult || e.id() == ID_shl || e.id() == ID_div) {
    or_exprt o = or_exprt(expr_protectedt::operandst());
    bool is_true = false;
    bool is_false = true;
    Forall_operands(op, e){
      const auto ab_op = is_expr_abstract(*op, width);
      if(ab_op.is_true())
      {
        is_true = true; is_false = false;
      }
      else if(!ab_op.is_false()){
        is_false = false;
        o.add_to_operands(ab_op);
      }
    }
    if(is_abstractable_type(e.type(), width))
    {
      is_false = false;
      e.set(ID_C_compute_overflow_bit, 1);
      o.add_to_operands(overflow_bitt(e));
    }
    if(is_true){
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, true_exprt()));
    }
    else if(is_false){
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, false_exprt()));
    } else {
      return static_cast<const exprt&>(e.add(ID_C_abstr_expr, o));
    }
  }
  else {
    UNREACHABLE;
  }
}


bool is_abstractable_name(const std::string name){
  return name.find("_cs_") == std::string::npos && name.find(CPROVER_PREFIX) != 0;
}

bool is_abstractable_type(typet& t, size_t width){
  if(t.find(ID_C_abstr_type).is_not_nil()){
    return t.get_int(ID_C_abstr_type);
  }
  if(const auto ibt = type_try_dynamic_cast<integer_bitvector_typet>(t)){
    t.set(ID_C_abstr_type, ibt->get_width() > width);
  }
  else if (const auto arr = type_try_dynamic_cast<array_typet>(t)){
    t.set(ID_C_abstr_type, is_abstractable_type(arr->element_type(), width));
  }
  else if (const auto str = type_try_dynamic_cast<struct_typet>(t)){
    bool abs = false;
    for(auto c : str->components()){
      if(!c.get_is_padding()){
        abs = is_abstractable_type(c.type(), width);
        if(abs)
          break;
      }
    }
    t.set(ID_C_abstr_type, abs);
  }
  else if (const auto uni = type_try_dynamic_cast<union_typet>(t)){
    bool abs = false; //should say true if exists abstractable field > width and all non abstractable field <= width
    t.set(ID_C_abstr_type, abs);
  }
  else {
    bool abs = false;
    t.set(ID_C_abstr_type, abs);
  }
  return t.get_int(ID_C_abstr_type);
}