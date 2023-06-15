//
// Created by giulio on 25/05/23.
//

#include <util/abstraction.h>

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "bitvector_types.h"
#include "byte_operators.h"
#include "c_types.h"
#include "cprover_prefix.h"
#include "pointer_offset_size.h"

#include <cmath>

#include "solvers/flattening/boolbv_width.h"
#include <util/namespace.h>

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
          e.id() == ID_forall || e.id() == ID_exists) {
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
        produce_nonabs(*op, targetEquation);
      }
    }
  } else if(e.id() == ID_not ||
          e.id() == ID_implies || e.id() == ID_and || e.id() == ID_or ||
          e.id() == ID_nand || e.id() == ID_nor || e.id() == ID_xor) {
    // NOT this op has abs_forbidden
    Forall_operands(op, e){
      set_if_abs_forbidden(*op, targetEquation);
    }
    ((*targetEquation.is_abs_forbidden)[e]) = false;
    (*targetEquation.produce_nonabs)[e] = true;
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
  } else if (e.id() == ID_constant || e.id() == ID_nondet_symbol) {
    (*targetEquation.is_abs_forbidden)[e] = false;
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

int how_many_bits(size_t x) {
  return ceil(log2(x));
}

bool is_signed(const typet &t){
  return to_integer_bitvector_type(t).smallest() < 0;
}

exprt or_simpl(const exprt &e0 = false_exprt{},
               const exprt &e1 = false_exprt{},
               const exprt &e2 = false_exprt{},
               const exprt &e3 = false_exprt{}){
  bool is_true = false;
  std::vector<exprt> o;
  is_true = e0.is_true() || e1.is_true() || e2.is_true() || e3.is_true();
  if(is_true)
    return true_exprt();
  if(!e0.is_false()) o.push_back(e0);
  if(!e1.is_false()) o.push_back(e1);
  if(!e2.is_false()) o.push_back(e2);
  if(!e3.is_false()) o.push_back(e3);
  if(o.empty())
    return false_exprt();
  else if(o.size() == 1)
    return o[0];
  else
    return or_exprt(o);
}

exprt and_simpl(const exprt &e0 = true_exprt{},
               const exprt &e1 = true_exprt{},
               const exprt &e2 = true_exprt{},
               const exprt &e3 = true_exprt{}){
  bool is_false = false;
  std::vector<exprt> a;
  is_false = e0.is_false() || e1.is_false() || e2.is_false() || e3.is_false();
  if(is_false)
    return false_exprt();
  if(!e0.is_true()) a.push_back(e0);
  if(!e1.is_true()) a.push_back(e1);
  if(!e2.is_true()) a.push_back(e2);
  if(!e3.is_true()) a.push_back(e3);
  if(a.empty())
    return true_exprt();
  else if(a.size() == 1)
    return a[0];
  else
    return and_exprt(a);
}

exprt map_and_or(std::vector<exprt>& ops, const std::function<exprt(exprt)>& fnc){
  std::vector<exprt> o;
  for(const auto &op: ops){
    const auto &fop = fnc(op);
    if(fop.is_true())
      return true_exprt();
    else if(!fop.is_false())
      o.push_back(fop);
  }
  if(o.empty())
    return false_exprt();
  else if(o.size() == 1)
    return o[0];
  else
    return or_exprt(o);
}

bool can_abstract(const exprt& op, symex_target_equationt &targetEquation){
  return !(*(*targetEquation.is_abs_forbidden)[op]);
}

bool can_abstract(const std::vector<exprt>& ops, symex_target_equationt &targetEquation){
  for(const auto &op:ops){
    if(!can_abstract(op, targetEquation))
      return false;
  }
  return true;
}

unsignedbv_typet get_abs_type(const typet &t, namespacet &ns){
  if(type_try_dynamic_cast<bool_typet>(t))
    return unsignedbv_typet(1);
  auto sz = numeric_cast<mp_integer>(*size_of_expr(t, ns))->to_long();
  return unsignedbv_typet(sz);
}

ssa_exprt get_abs_symbol(const ssa_exprt &orig, namespacet &ns){
  auto ident = as_string(orig.get_identifier());
  auto idx = ident.find_last_of("::");
  if(idx == std::string::npos)
    idx = 0;
  else
    idx += 2;
  auto abstr_ident = ident.substr(0,idx) + "__ABSTR__" + ident.substr(idx);
  return ssa_exprt(symbol_exprt(abstr_ident, get_abs_type(orig.type(), ns)));
}
constant_exprt get_zero_sm_symbol(const typet &t, namespacet &ns){
  return get_abs_type(t, ns).smallest_expr();
}
constant_exprt get_one_sm_symbol(const typet &t, namespacet &ns){
  return get_abs_type(t, ns).largest_expr();
}
ssa_exprt get_random_bit(const nondet_symbol_exprt &orig){
  auto ident = as_string(orig.get_identifier());
  auto idx = ident.find_last_of("::");
  if(idx == std::string::npos)
    idx = 0;
  else
    idx += 2;
  auto abstr_ident = ident.substr(0,idx) + "__NONDET__" + ident.substr(idx);
  return ssa_exprt(symbol_exprt(abstr_ident, unsignedbv_typet(1)));
}
exprt update_sm(const exprt &bit, const typet &to_cover_tp, namespacet &ns){
  PRECONDITION(can_cast_type<unsignedbv_typet>(bit.type()) && to_unsignedbv_type(bit.type()).get_width() == 1);
  auto to_cover_sm = get_abs_type(to_cover_tp, ns);
  if(auto const c = expr_try_dynamic_cast<constant_exprt>(bit)){
    if(c->is_zero()){
      return unsignedbv_typet(to_cover_sm.get_width()).smallest_expr();
    } else {
      return unsignedbv_typet(to_cover_sm.get_width()).largest_expr();
    }
  }
  return replication_exprt{
    from_integer(to_cover_sm.get_width(), size_type()), bit, to_cover_sm};
}
unary_exprt get_sm(const exprt &sm){
  return {ID_reduction_or, sm, unsignedbv_typet(1)};
}
/*exprt max_sm(const exprt &sm, const typet &to_cover_tp, namespacet &ns){
  auto bit = get_sm(sm);
  return update_sm(bit, to_cover_tp, ns);
}*/

exprt abstr_check(const exprt &e, bool abs_result, const size_t width, symex_target_equationt &targetEquation, namespacet &ns, boolbv_widtht &bv_width){
  exprt abs_check;
  // MARK ALL EXPRESSION GENERATED BY THIS FUNCTION AS "abstr_check_generated" AND "produce_no_abstract"
  const auto map_key = std::make_pair(e, abs_result);
  if((*targetEquation.is_abstract)[map_key])
    return *(*targetEquation.is_abstract)[map_key];
  else if(!abs_result && (!(*targetEquation.produce_nonabs)[e] || !*(*targetEquation.produce_nonabs)[e])){
    PRECONDITION(false);
  } else if(abs_result && *(*targetEquation.is_abs_forbidden)[e]){
    PRECONDITION(false);
  }
  else if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    bool has_sm = !*(*targetEquation.is_abs_forbidden)[e];
    bool needs_bounds_failure = abs_result && is_abstractable_type(ssa->type(), width, targetEquation);
    if(needs_bounds_failure)
      (*targetEquation.compute_bounds_failure)[e] = true;
    if(has_sm){
      if(needs_bounds_failure)
        abs_check = bitor_exprt(get_abs_symbol(*ssa, ns), update_sm(bounds_failuret(*ssa, width), ssa->type(), ns));
      else
        abs_check = get_abs_symbol(*ssa, ns);
    } else {
      if(needs_bounds_failure)
        abs_check = update_sm(bounds_failuret(*ssa, width), ssa->type(), ns);
      else
        abs_check = get_zero_sm_symbol(ssa->type(), ns);
    }
  } else if (auto cons = expr_try_dynamic_cast<constant_exprt>(e)) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(cons->type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      auto x = numeric_cast<mp_integer>(*cons);
      auto tp = to_integer_bitvector_type(cons->type()).smallest() < 0 ? (integer_bitvector_typet) signedbv_typet(width) : unsignedbv_typet(width);
      abs_check = (x < tp.smallest() || x > tp.largest())? get_one_sm_symbol(cons->type(), ns) : get_zero_sm_symbol(cons->type(), ns);
    } else {
      abs_check = get_zero_sm_symbol(cons->type(), ns);
    }
  } else if (const auto nondet = expr_try_dynamic_cast<nondet_symbol_exprt>(e)) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      auto ndbit = get_random_bit(*nondet);
      abs_check = update_sm(ndbit, nondet->type(), ns);
    } else {
      abs_check = get_zero_sm_symbol(e.type(), ns);
    }
  } else if (e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult ||
          e.id() == ID_shl || e.id() == ID_div || e.id() == ID_rol ||
          e.id() == ID_ror || e.id() == ID_power || e.id() == ID_mod) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
    }
    auto op_ok = bitor_exprt(get_sm(abstr_check(e.operands()[0], abs_result, width, targetEquation, ns, bv_width)),
                             get_sm(abstr_check(e.operands()[1], abs_result, width, targetEquation, ns, bv_width)));
    if(needs_bounds_failure)
      op_ok = bitor_exprt(op_ok, bounds_failuret(e, width));

    abs_check = update_sm(op_ok, e.type(), ns);
  } else if (e.id() == ID_ge || e.id() == ID_gt || e.id() == ID_le ||
          e.id() == ID_lt || e.id() == ID_equal || e.id() == ID_notequal) {
    bool do_operands_with_abstraction = abs_result && can_abstract(e.operands(), targetEquation);
    if(!do_operands_with_abstraction)
      assert(*(*targetEquation.produce_nonabs)[e]);
    auto op_ok = bitor_exprt(get_sm(abstr_check(e.operands()[0], do_operands_with_abstraction, width, targetEquation, ns, bv_width)),
                             get_sm(abstr_check(e.operands()[1], do_operands_with_abstraction, width, targetEquation, ns, bv_width)));
    abs_check = update_sm(op_ok, e.type(), ns);
  } else if (const auto be = expr_try_dynamic_cast<byte_extract_exprt>(e)) {
    // see if you can restrict the offset search somehow (e.g., offset is limited to x bits)
    // maybe, have a look on the higher literals of offset
    exprt offset_abs = get_sm(abstr_check(be->offset(), abs_result, width, targetEquation, ns, bv_width));
    exprt op_sm = abstr_check(be->op(), abs_result, width, targetEquation, ns, bv_width);
    auto extract_op_sm = byte_extract_exprt(ID_byte_extract_little_endian, op_sm, be->offset(), 1, get_abs_type(be->type(), ns));
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_exprt(update_sm(bitor_exprt(bounds_failuret(*be, width), offset_abs), e.type(), ns), extract_op_sm);
    } else {
      abs_check = bitor_exprt(update_sm(offset_abs, e.type(), ns), extract_op_sm);
    }
  } else if (const auto eb = expr_try_dynamic_cast<extractbits_exprt>(e)) {
    auto const maybe_upper_as_int = numeric_cast<mp_integer>(eb->upper());
    auto const maybe_lower_as_int = numeric_cast<mp_integer>(eb->lower());
    auto const lower_byte = (*maybe_lower_as_int/8).to_long();
    auto const upper_byte = ((*maybe_upper_as_int+6)/8).to_long(); //ceil((*maybe_upper_as_int-1)/8)
    exprt op_sm = abstr_check(eb->src(), abs_result, width, targetEquation, ns, bv_width);
    auto extract_op_sm = extractbits_exprt(op_sm, upper_byte, lower_byte, unsignedbv_typet(upper_byte - lower_byte + 1));
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_exprt(update_sm(bounds_failuret(*eb, width), extract_op_sm.type(), ns), extract_op_sm);
    } else {
      abs_check = extract_op_sm;
    }
  } else if (const auto ebit = expr_try_dynamic_cast<extractbit_exprt>(e)) {
    auto const maybe_index_as_int = numeric_cast<mp_integer>(ebit->index());
    auto const index_byte = (*maybe_index_as_int/8).to_long();
    exprt op_sm = abstr_check(ebit->src(), abs_result, width, targetEquation, ns, bv_width);
    auto extract_op_sm = extractbit_exprt(op_sm, index_byte);
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_exprt(update_sm(bounds_failuret(*eb, width), extract_op_sm.type(), ns), extract_op_sm);
    } else {
      abs_check = extract_op_sm;
    }
  } else if (const auto bu = expr_try_dynamic_cast<byte_update_exprt>(e)) {
    // see if you can restrict the offset search somehow (e.g., offset is limited to x bits)
    // maybe, have a look on the higher literals of offset
    exprt offset_abs = get_sm(abstr_check(bu->offset(), abs_result, width, targetEquation, ns, bv_width));
    exprt op_sm = abstr_check(bu->op(), abs_result, width, targetEquation, ns, bv_width);
    exprt value_sm = abstr_check(bu->value(), abs_result, width, targetEquation, ns, bv_width);
    if(op_sm.is_nil() || offset_abs.is_nil() || value_sm.is_nil())
      abs_check.make_nil();
    else
    {
      bool needs_bounds_failure =
        abs_result && is_abstractable_type(e.type(), width, targetEquation);
      auto bupdate_sm = byte_update_exprt(
        ID_byte_update_little_endian, op_sm, bu->offset(), value_sm, 1);
      if(needs_bounds_failure)
      {
        UNREACHABLE;
        /*(*targetEquation.compute_bounds_failure)[e] = true;
        abs_check = bitor_exprt(
          update_sm(
            bitor_exprt(bounds_failuret(*bu, width), offset_abs),
            e.type(),
            ns),
          bupdate_sm);*/
      }
      else
      {
        abs_check =
          bitor_exprt(update_sm(offset_abs, e.type(), ns), bupdate_sm);
      }
      assert((to_integer_bitvector_type(abs_check.type()).get_width() == get_abs_type(e.type(), ns).get_width()));
    }
  } else if (const auto ife = expr_try_dynamic_cast<if_exprt>(e))
  {
    bool abs_result_cond = can_abstract(ife->cond(), targetEquation);
    exprt cond_abs_bits = abstr_check(
      ife->cond(), abs_result_cond, width, targetEquation, ns, bv_width); //multiple bits
    if(cond_abs_bits.is_true()){
      abs_check = true_exprt();
    } else {
      auto then_abs = abstr_check(ife->true_case(), abs_result, width, targetEquation, ns, bv_width);
      auto else_abs = abstr_check(ife->false_case(), abs_result, width, targetEquation, ns, bv_width);
      abs_check = if_exprt(ife->cond(), then_abs, else_abs);
      if(!cond_abs_bits.is_false()){
        abs_check = bitor_exprt(update_sm(get_sm(cond_abs_bits), ife->type(), ns), abs_check);
      }
    }
  } else if (const auto ae = expr_try_dynamic_cast<and_exprt>(e))
  {
    //(foreach i: ci is not sound or ci is true) and (exists i: ci is not sound)
    exprt foreach_not_sound_or_true = get_one_sm_symbol(unsigned_char_type(), ns);
    exprt exists_unsound = get_zero_sm_symbol(unsigned_char_type(), ns);
    bool first = true;
    for(const auto &op: ae->operands()){
      exprt check = abstr_check(op, can_abstract(op, targetEquation), width, targetEquation, ns, bv_width);
      if(first){
        foreach_not_sound_or_true = bitor_exprt(check, typecast_exprt::conditional_cast(op, unsignedbv_typet(1)));
        exists_unsound = check;
        first = false;
      } else {
        foreach_not_sound_or_true = bitand_exprt(foreach_not_sound_or_true, bitor_exprt(check, typecast_exprt::conditional_cast(op, unsignedbv_typet(1))));
        exists_unsound = bitor_exprt(exists_unsound, check);
      }
    }
    abs_check = bitand_exprt(foreach_not_sound_or_true, exists_unsound);
  } else if (const auto oe = expr_try_dynamic_cast<or_exprt>(e))
  {
    //(foreach i: ci is not sound or ci is false) and (exists i: ci is not sound)
    exprt foreach_not_sound_or_false = get_one_sm_symbol(unsigned_char_type(), ns);
    exprt exists_unsound = get_zero_sm_symbol(unsigned_char_type(), ns);
    bool first = true;
    for(const auto &op: oe->operands()){
      exprt check = abstr_check(op, can_abstract(op, targetEquation), width, targetEquation, ns, bv_width);
      if(first){
        foreach_not_sound_or_false = bitor_exprt(check, bitnot_exprt(typecast_exprt::conditional_cast(op, unsignedbv_typet(1))));
        exists_unsound = check;
        first = false;
      } else {
        foreach_not_sound_or_false = bitand_exprt(foreach_not_sound_or_false, bitor_exprt(check, bitnot_exprt(typecast_exprt::conditional_cast(op, unsignedbv_typet(1)))));
        exists_unsound = bitor_exprt(exists_unsound, check);
      }
    }
    abs_check = bitand_exprt(foreach_not_sound_or_false, exists_unsound);
  } else if (const auto ne = expr_try_dynamic_cast<not_exprt>(e))
  {
    //(op is not sound)
    abs_check = abstr_check(ne->op(), can_abstract(ne->op(), targetEquation), width, targetEquation, ns, bv_width);
  } else if (const auto impl = expr_try_dynamic_cast<implies_exprt>(e))
  {
    //A -> B : (B is not sound or B is false) and (A is not sound or A is true) and (B is not sound or A is not sound)
    exprt checkA = abstr_check(
      impl->lhs(),
      can_abstract(impl->lhs(), targetEquation),
      width,
      targetEquation,
      ns, bv_width);
    exprt checkB = abstr_check(
      impl->rhs(),
      can_abstract(impl->rhs(), targetEquation),
      width,
      targetEquation,
      ns, bv_width);
    exprt A = typecast_exprt::conditional_cast(impl->lhs(), unsignedbv_typet(1));
    exprt B = typecast_exprt::conditional_cast(impl->rhs(), unsignedbv_typet(1));

    abs_check = bitand_exprt(
      bitor_exprt(checkA, checkB),
      bitand_exprt(
        bitor_exprt(checkB, bitnot_exprt(B)),
        bitor_exprt(checkA, A)));
  } else if (const auto cast = expr_try_dynamic_cast<typecast_exprt>(e))
  {
    bool needs_bounds_failure =
      abs_result && is_abstractable_type(e.type(), width, targetEquation);
    auto op_check = (get_sm(abstr_check(cast->op(), abs_result, width, targetEquation, ns, bv_width)));

    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = update_sm(
          bitor_exprt(op_check, bounds_failuret(*cast, width)),
          cast->type(),
          ns);
    }
    else
    {
      abs_check = update_sm(
        op_check,
        cast->type(),
        ns);
    }
  } else if (const auto str = expr_try_dynamic_cast<struct_exprt>(e))
  {
    abs_check = get_zero_sm_symbol(e.type(), ns);
    auto op_it=str->operands().begin();
    size_t bitIdx = 0;
    //for(const auto &c_def : to_struct_type(str->type()).components()){
    while(op_it != str->operands().end()){
      const auto& op = *op_it;
      size_t sz = bv_width(op.type());
      //if(!c_def.get_is_padding()){
        auto op_ab = abstr_check(op, abs_result, width, targetEquation, ns, bv_width);
        abs_check = byte_update_exprt(ID_byte_update_little_endian, abs_check, from_integer(bitIdx/8, size_type()), op_ab, 1);
      //}
      bitIdx += sz;
      op_it++;
    }
  } else if (const auto aof = expr_try_dynamic_cast<array_of_exprt>(e))
  {
    const auto array_smtype = get_abs_type(e.type(), ns);
    const auto elem_smtype = get_abs_type(aof->what().type(), ns);
    const auto copies = array_smtype.get_width()/std::max((size_t)1, elem_smtype.get_width());
    const auto elem_sm = abstr_check(aof->what(), abs_result, width, targetEquation, ns, bv_width);
    abs_check = replication_exprt(from_integer(copies, size_type()), elem_sm, array_smtype);
  } else if (const auto idx = expr_try_dynamic_cast<index_exprt>(e))
  {
    const auto idx_sm = get_sm(abstr_check(
      idx->index(),
      can_abstract(idx->index(), targetEquation),
      width,
      targetEquation,
      ns,
      bv_width));
    const auto array_sm = get_sm(abstr_check(
      idx->array(), abs_result, width, targetEquation, ns, bv_width));
    const auto elem_smtype = get_abs_type(idx->type(), ns);
    const auto elem_width =
      from_integer(elem_smtype.get_width(), idx->index().type());
    abs_check = bitor_exprt(
      byte_extract_exprt(
        ID_byte_extract_little_endian,
        array_sm,
        mult_exprt(elem_width, idx->index()),
        1,
        elem_smtype),
      update_sm(idx_sm, idx->type(), ns));
  } else if (const auto poff = expr_try_dynamic_cast<pointer_offset_exprt>(e))
  {
    const auto ptr_sm = get_sm(abstr_check(
      poff->pointer(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width));
    abs_check = update_sm(ptr_sm, poff->type(), ns);
  } else if (const auto pobj = expr_try_dynamic_cast<pointer_object_exprt>(e))
  {
    const auto ptr_sm = get_sm(abstr_check(
      pobj->pointer(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width));
    abs_check = update_sm(ptr_sm, pobj->type(), ns);
  } else if (const auto arr = expr_try_dynamic_cast<array_exprt>(e))
  {
    std::vector<exprt> elems_sm;
    for(const auto &op: arr->operands()){
      elems_sm.push_back(abstr_check(op, abs_result, width, targetEquation, ns, bv_width));
    }
    abs_check = concatenation_exprt(elems_sm, get_abs_type(arr->type(), ns));
  } else if (const auto with = expr_try_dynamic_cast<with_exprt>(e))
  {
    const auto &tp = with->old().type();
    const auto old_sm = abstr_check(
      with->old(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width);
    const auto where_sm_extended = update_sm(get_sm(abstr_check(
      with->where(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width)), with->old().type(), ns);
    const auto new_sm = abstr_check(
      with->new_value(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width);
    const auto new_sm_width = get_abs_type(with->new_value().type(), ns).get_width();
    //const auto new_sm_width_expr = from_integer(new_sm_width, unsigned_int_type());
    if(tp.id() == ID_array)
    {
      if(can_abstract(with->where(), targetEquation))
      {
        auto bits_index_type = std::min(
          to_integer_bitvector_type(with->where().type()).get_width(),
          width + how_many_bits(new_sm_width));
        auto index_type =
          is_signed(with->where().type())
            ? (integer_bitvector_typet)signedbv_typet(bits_index_type)
            : unsignedbv_typet(bits_index_type);
        auto old_sm_index = mult_exprt(
          typecast_exprt::conditional_cast(with->where(), index_type),
          from_integer(new_sm_width, index_type));
        abs_check = bitor_exprt(
          byte_update_exprt(
            ID_byte_update_little_endian, old_sm, old_sm_index, new_sm, 1),
          where_sm_extended);
      }
      else
      {
        auto old_sm_index = mult_exprt(
          with->where(), from_integer(new_sm_width, with->where().type()));
        abs_check = bitor_exprt(
          byte_update_exprt(
            ID_byte_update_little_endian, old_sm, old_sm_index, new_sm, 1),
          where_sm_extended);
      }
    } else {
      UNIMPLEMENTED;
    }
    abs_check = bitor_exprt(where_sm_extended, abs_check);
  } else if (const auto aoff = expr_try_dynamic_cast<address_of_exprt>(e))
  {
    abs_check = get_zero_sm_symbol(aoff->type(), ns);
  } else if (const auto member = expr_try_dynamic_cast<member_exprt>(e))
  {
    const typet &compound_type = member->compound().type();
    if(compound_type.id() == ID_struct_tag || compound_type.id() == ID_struct)
    {
      const struct_typet &struct_op_type =
        compound_type.id() == ID_struct_tag
          ? ns.follow_tag(to_struct_tag_type(compound_type))
          : to_struct_type(compound_type);
      const auto &member_bits =
        bv_width.get_member(struct_op_type, member->get_component_name());
      auto op_ab = abstr_check(member->op(), abs_result, width, targetEquation, ns, bv_width);
      abs_check = byte_extract_exprt(ID_byte_extract_little_endian, op_ab, from_integer(member_bits.offset/8, unsigned_int_type()), 1, get_abs_type(e.type(), ns));
    } else {
      UNIMPLEMENTED;
    }
  } else {
    UNIMPLEMENTED;
    abs_check.make_nil();
  }
  assert((to_integer_bitvector_type(abs_check.type()).get_width() == get_abs_type(e.type(), ns).get_width()));
  targetEquation.merge_irep(abs_check);
  (*targetEquation.is_abstract)[map_key] = std::move(abs_check);
  return *(*targetEquation.is_abstract)[map_key];
}
#if 0
exprt abstr_check_old(exprt &e, bool abs_result, const size_t width, symex_target_equationt &targetEquation){
  exprt abs_check;
  const auto map_key = std::make_pair(e, abs_result);
  if((*targetEquation.is_abstract)[map_key])
    return *(*targetEquation.is_abstract)[map_key];
  else if(abs_result && !*(*targetEquation.produce_nonabs)[e]){
    INVARIANT(!(abs_result && !*(*targetEquation.produce_nonabs)[e]), "abs_result requires produce_nonabs");
  } else if(!abs_result && *(*targetEquation.is_abs_forbidden)[e]){
    INVARIANT(!(!abs_result && *(*targetEquation.is_abs_forbidden)[e]), "is_abs_forbidden incompatible with abs_result");
  } else if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    bool has_sm = !*(*targetEquation.is_abs_forbidden)[e];
    bool needs_bounds_failure = abs_result && is_abstractable_type(ssa->type(), width);
    if(needs_bounds_failure)
      *(*targetEquation.compute_bounds_failure)[e] = true;
    if(has_sm){
      if(needs_bounds_failure)
        abs_check = or_exprt(is_abstractt(*ssa), bounds_failuret(*ssa));
      else
        abs_check = is_abstractt(*ssa);
    } else {
      if(needs_bounds_failure)
        abs_check = bounds_failuret(*ssa);
      else
        abs_check = false_exprt();
    }
  } else if (e.id() == ID_constant || e.id() == ID_nondet_symbol) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width);
    if(needs_bounds_failure)
    {
      *(*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bounds_failuret(e);
    } else {
      abs_check = false_exprt();
    }
  } else if (e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult ||
          e.id() == ID_shl || e.id() == ID_div || e.id() == ID_rol ||
          e.id() == ID_ror || e.id() == ID_power) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width);
    if(needs_bounds_failure)
    {
      *(*targetEquation.compute_bounds_failure)[e] = true;
    }
    abs_check = or_simpl(abstr_check(e.operands()[0], abs_result, width, targetEquation),
                    abstr_check(e.operands()[1], abs_result, width, targetEquation),
                    needs_bounds_failure?(exprt)bounds_failuret(e):false_exprt());
  } else if (e.id() == ID_unary_minus || e.id() == ID_bitreverse || e.id() == ID_bswap ||
          e.id() == ID_abs || e.id() == ID_pointer_offset) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width);
    if(needs_bounds_failure)
    {
      *(*targetEquation.compute_bounds_failure)[e] = true;
    }
    abs_check = or_simpl(abstr_check(e.operands()[0], abs_result, width, targetEquation),
                         needs_bounds_failure?(exprt)bounds_failuret(e):false_exprt());
  } else if (const auto cast = expr_try_dynamic_cast<typecast_exprt>(e)) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(cast->type(), width) &&
                                !is_abstractable_type(cast->op().type(), width);
    if(needs_bounds_failure)
    {
      *(*targetEquation.compute_bounds_failure)[e] = true;
    }
    abs_check = or_simpl(abstr_check(e.operands()[0], abs_result, width, targetEquation),
                         needs_bounds_failure?(exprt)bounds_failuret(e):false_exprt());
  } else if (e.id() == ID_shr || e.id() == ID_lshr || e.id() == ID_ashr ||
          e.id() == ID_array || e.id() == ID_array_of || e.id() == ID_bitand ||
          e.id() == ID_bitor || e.id() == ID_bitxor || e.id() == ID_bitnand ||
          e.id() == ID_bitnor || e.id() == ID_bitxnor || e.id() == ID_bitnot ||
          e.id() == ID_complex || e.id() == ID_complex_imag ||
          e.id() == ID_complex_real || e.id() == ID_concatenation ||
          e.id() == ID_floatbv_mod || e.id() == ID_floatbv_rem ||
          e.id() == ID_floatbv_plus || e.id() == ID_floatbv_minus ||
          e.id() == ID_floatbv_mult || e.id() == ID_floatbv_div ||
          e.id() == ID_let || e.id() == ID_member || e.id() == ID_onehot ||
          e.id() == ID_onehot0 || e.id() == ID_reduction_or ||
          e.id() == ID_reduction_and || e.id() == ID_reduction_nand ||
          e.id() == ID_reduction_nor || e.id() == ID_reduction_xor ||
          e.id() == ID_reduction_xnor || e.id() == ID_struct || e.id() == ID_union ||
          e.id() == ID_update || e.id() == ID_vector || e.id() == ID_with ||
          e.id() == ID_pointer_object || e.id() == ID_byte_extract_little_endian ||
          e.id() == ID_byte_extract_big_endian || e.id() == ID_extractbit ||
          e.id() == ID_extractbits || e.id() == ID_byte_update_little_endian ||
          e.id() == ID_byte_update_big_endian ||
          e.id() == ID_overflow_result_minus || e.id() == ID_overflow_result_plus ||
          e.id() == ID_overflow_result_mult || e.id() == ID_overflow_result_unary_minus ||
          e.id() == ID_overflow_result_shl ||
          e.id() == ID_ieee_float_equal || e.id() == ID_ieee_float_notequal ||
          e.id() == ID_replication) {
    abs_check = map_and_or(
      e.operands(),
      [abs_result, width, &targetEquation](exprt ex)
      { return abstr_check(ex, abs_result, width, targetEquation); });
  } else if (e.id() == ID_overflow_minus ||
          e.id() == ID_overflow_plus || e.id() == ID_overflow_mult  ||
          e.id() == ID_overflow_unary_minus || e.id() == ID_overflow_shl ||
          e.id() == ID_cond || e.id() == ID_forall || e.id() == ID_exists ||
          e.id() == ID_not || e.id() == ID_implies || e.id() == ID_and ||
          e.id() == ID_or || e.id() == ID_nand || e.id() == ID_nor ||
          e.id() == ID_xor){
    bool do_abs = can_abstract(e.operands(), targetEquation);
    abs_check = map_and_or(
      e.operands(),
      [do_abs, width, &targetEquation](exprt ex)
      { return abstr_check(ex, do_abs, width, targetEquation); });
  } else if(e.id() == ID_address_of) {
    abs_check = false_exprt();
  } else if(e.id() == ID_ge || e.id() == ID_le || e.id() == ID_gt ||
          e.id() == ID_lt || e.id() == ID_equal || e.id() == ID_notequal) {
    bool request_full = *(*targetEquation.produce_nonabs)[e];
    abs_check = map_and_or(
      e.operands(),
      [request_full, width, &targetEquation](exprt ex)
      { return abstr_check(ex, !request_full, width, targetEquation); });
  } else if(e.id() == ID_case){
    // exists op[o] with abs_forbidden AND (o=0 OR o is odd) <=> Check full every op[o'] (o'=0 OR o' is odd) (otherwise abstr)
    // Check then and else at abs_result level every op[e'] (e>0 AND e' is even)
    bool abstr_o = !*(*targetEquation.is_abs_forbidden)[e.operands()[0]];
    for(size_t i=1; abstr_o && i<e.operands().size(); i+=2)
      abstr_o = !*(*targetEquation.is_abs_forbidden)[e.operands()[i]];
    int i = 0;
    abs_check = map_and_or(
      e.operands(),
      [&i, abstr_o, abs_result, width, &targetEquation](exprt ex)
      { return abstr_check(ex, ((i == 0 || i % 2 == 1)?(++i, abstr_o):(++i, abs_result)), width, targetEquation); });
  } else if(const auto ifexp = expr_try_dynamic_cast<if_exprt>(e)){
    // Check then and else at abs_result level + Check e.cond() at (e.cond() has abs forbidden? full:reduced)
    bool abstr_cond = !*(*targetEquation.is_abs_forbidden)[ifexp->cond()];
    abs_check = or_simpl(abstr_check(ifexp->cond(), abstr_cond, width, targetEquation),
                         abstr_check(ifexp->true_case(), abs_result, width, targetEquation),
                         abstr_check(ifexp->false_case(), abs_result, width, targetEquation));
  } else if(const auto index = expr_try_dynamic_cast<index_exprt>(e)){
    // Check array at abs_result level + Check e.index() at (e.index() has abs forbidden? full:reduced)
    bool abstr_index = !*(*targetEquation.is_abs_forbidden)[index->index()];
    abs_check = or_simpl(abstr_check(index->array(), abs_result, width, targetEquation),
                         abstr_check(index->index(), abstr_index, width, targetEquation));
  } else {
    UNREACHABLE;
  }
  targetEquation.merge_irep(abs_check);
  *(*targetEquation.is_abstract)[map_key] = std::move(abs_check);
  return *(*targetEquation.is_abstract)[map_key];
}
#endif

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

void apply_approx(symex_target_equationt &targetEquation, size_t width, namespacet &ns)
{
  boolbv_widtht bv_width = boolbv_widtht(ns);
  symex_target_equationt::SSA_stepst abs_steps;
  targetEquation.is_type_abstract = {std::map<typet,optionalt<bool>>()};
  targetEquation.is_abs_forbidden = {std::map<exprt,optionalt<bool>>()};
  targetEquation.produce_nonabs = {std::map<exprt,optionalt<bool>>()};
  targetEquation.is_abstract = {std::map<std::pair<exprt, bool>,optionalt<exprt>>()};
  targetEquation.compute_bounds_failure = {std::map<exprt,optionalt<bool>>()};
  for(SSA_stept &step:targetEquation.SSA_steps){
    set_if_abs_forbidden(step.guard, targetEquation);
    switch(step.type)
    {
    case goto_trace_stept::typet::NONE:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ASSIGNMENT:{
      bool lhs_abs_forbidden = set_if_abs_forbidden(step.ssa_lhs, targetEquation);
      set_if_abs_forbidden(step.ssa_rhs, targetEquation);
      if(lhs_abs_forbidden)
      {
        produce_nonabs(step.ssa_lhs, targetEquation);
        produce_nonabs(step.ssa_rhs, targetEquation);
      }
      abs_steps.emplace_back(step);
      // TODO here only to test abstraction
      if(!lhs_abs_forbidden)
      {
        auto abstr_lhs = get_abs_symbol(step.ssa_lhs, ns);
        auto abstr_rhs = abstr_check(
          step.ssa_rhs, !lhs_abs_forbidden, width, targetEquation, ns, bv_width);
        if(abstr_rhs.is_nil()){ // only because instr is incomplete
          abs_steps.emplace_back(SSA_assignment_stept{
            step.source,
            true_exprt(),
            abstr_lhs,
            nil_exprt(),
            nil_exprt(),
            from_integer(-1, abstr_lhs.type()),
            step.assignment_type});
        } else {
          abs_steps.emplace_back(SSA_assignment_stept{
            step.source,
            true_exprt(),
            abstr_lhs,
            nil_exprt(),
            nil_exprt(),
            abstr_rhs,
            step.assignment_type});
        }
        targetEquation.merge_ireps(abs_steps.back());
      }
      /*auto abstr_lhs = is_abstractt(step.ssa_lhs);

        //ssa_exprt(symbol_exprt("ABSTR_" + as_string(step.ssa_lhs.get_identifier()), bool_typet()));
      auto cant_guard_or_guard_and_cant_rhs = or_simpl(is_expr_abstract(step.guard, width),
                                                       and_simpl(step.guard, is_expr_abstract(step.ssa_rhs, width)));
      abs_steps.emplace_back(SSA_assignment_stept{step.source,
                                                  true_exprt(),
                                                  abstr_lhs,
                                                  nil_exprt(),
                                                  nil_exprt(),
                                                  cant_guard_or_guard_and_cant_rhs,
                                                  step.assignment_type});
      targetEquation.merge_ireps(abs_steps.back());*/

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

#if 0
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
      o.add_to_operands(bounds_failuret(e));
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
#endif

bool is_abstractable_name(const std::string name){
  return name.find("_cs_") == std::string::npos && name.find(CPROVER_PREFIX) != 0;
}

bool is_abstractable_type(const typet& t, size_t width, symex_target_equationt &targetEquation){
  if((*targetEquation.is_type_abstract)[t])
    return *((*targetEquation.is_type_abstract)[t]);

  if(const auto ibt = type_try_dynamic_cast<integer_bitvector_typet>(t)){
    (*targetEquation.is_type_abstract)[t] = ibt->get_width() > width;
  }
  else if (const auto arr = type_try_dynamic_cast<array_typet>(t)){
    (*targetEquation.is_type_abstract)[t] = is_abstractable_type(arr->element_type(), width, targetEquation);
  }
  else if (const auto str = type_try_dynamic_cast<struct_typet>(t)){
    bool abs = false;
    for(auto c : str->components()){
      if(!c.get_is_padding()){
        abs = is_abstractable_type(c.type(), width, targetEquation);
        if(abs)
          break;
      }
    }
    (*targetEquation.is_type_abstract)[t] = abs;
  }
  else if (const auto uni = type_try_dynamic_cast<union_typet>(t)){
    bool abs = false; //should say true if exists abstractable field > width and all non abstractable field <= width
    (*targetEquation.is_type_abstract)[t] = abs;
  }
  else {
    bool abs = false;
    (*targetEquation.is_type_abstract)[t] = abs;
  }
  return *((*targetEquation.is_type_abstract)[t]);
}