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
    produce_nonabs(repl->times(), targetEquation);
  } else if(const auto cast = expr_try_dynamic_cast<typecast_exprt>(e)){
    (*targetEquation.produce_nonabs)[e] = true;
    produce_nonabs(cast->op(), targetEquation);
  } else if(const auto bf = expr_try_dynamic_cast<bounds_failuret>(e)) {

  } else {
    UNREACHABLE;
  }
}

bool test_pattern_ptr_index_times_offset(const exprt &e)
{
  /* special pattern: a + (idx * const)
   * where a is a pointer and const is the size of a's elements. Produce it fully,
   * it is used in expressions like &a[idx] */
  if(
    e.type().id() == ID_pointer && e.id() == ID_plus &&
    e.operands()[1].id() == ID_mult &&
    is_ssa_expr(e.operands()[1].operands()[0]) &&
    e.operands()[1].operands()[1].is_constant())
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool test_pattern_ptr_offset(const exprt &e)
{
  /* special pattern: a + const
   * where a is a pointer and const is a constant offset. Produce it fully,
   * it is used in expressions like &a.field */
  if(
    e.type().id() == ID_pointer && e.id() == ID_plus &&
    e.operands()[1].is_constant())
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool test_pattern_ptroffset_const(const exprt &e)
{
  /* special patterns: a + const and const + a
   * where a is POINTER_OFFSET and const is a constant offset. Produce it fully,
   * it is used in byte_update */
  if(
    e.id() == ID_plus &&
    ((e.operands()[0].is_constant() && can_cast_expr<pointer_offset_exprt>(e.operands()[1])) ||
     (e.operands()[1].is_constant() && can_cast_expr<pointer_offset_exprt>(e.operands()[0]))))
  {
    return true;
  }
  else
  {
    return false;
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
    if(forbOp || test_pattern_ptr_index_times_offset(e) || test_pattern_ptr_offset(e) || test_pattern_ptroffset_const(e)){
      (*targetEquation.produce_nonabs)[e] = true;
      Forall_operands(op, e){
        produce_nonabs(*op, targetEquation);
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
    if(forbOp){
      (*targetEquation.produce_nonabs)[e] = true;
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
    //(*targetEquation.produce_nonabs)[e] = true;
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
  } else if(e.id() == ID_member_name){
    // member names do not affect abstractability
    ((*targetEquation.is_abs_forbidden)[e]) =  false;
    (*targetEquation.produce_nonabs)[e] = false;
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

/*void elevate_ors_rec(const exprt &e0, std::vector<exprt> items){
  if(auto ors = expr_try_dynamic_cast<or_exprt>(e0)){
    for(auto &o : ors->operands()){
      items.push_back(o);
    }
  } else if(auto red = expr_try_dynamic_cast<unary_exprt>(e0)){
    if(red->op().id() == ID_reduction_or){
      for(auto &o : red->operands()){
        items.push_back(o);
      }
    }
  }
}*/

exprt bitor_simpl_onebit(symex_target_equationt &targetEquationt,
  std::vector<exprt> &o){
  std::vector<exprt> o_stack = o; //things to process, all unsigned{1}
  std::unordered_set<exprt, irep_hash> clean_o; //every expression is a boolean to be or-ed
  std::unordered_set<bounds_failuret, irep_hash> clean_bf; //bounds failures without conditions
  while(!o_stack.empty()){
    const exprt ex = o_stack.back();
    PRECONDITION(ex.type().id() == ID_unsignedbv && to_unsignedbv_type(ex.type()).get_width() == 1);
    o_stack.pop_back();
    if(auto bito = expr_try_dynamic_cast<bitor_exprt>(ex)){
      o_stack.insert(o_stack.end(), bito->operands().begin(), bito->operands().end());
    } else if(can_cast_expr<typecast_exprt>(ex) && can_cast_expr<or_exprt>(to_typecast_expr(ex).op())){
      for(const auto &op : to_typecast_expr(ex).op().operands()){
        o_stack.push_back(typecast_exprt(op, unsignedbv_typet{1}));
        targetEquationt.merge_irep.merged1L(o_stack.back());
      }
    } else if(can_cast_expr<bitor_exprt>(ex)){
      for(const auto &op : to_bitor_expr(ex).operands()){
        o_stack.push_back(op);
      }
    } else if(can_cast_expr<typecast_exprt>(ex) && can_cast_expr<typecast_exprt>(to_typecast_expr(ex).op())){
      o_stack.push_back(to_typecast_expr(to_typecast_expr(ex).op()).op());
    } else if(can_cast_expr<typecast_exprt>(ex) && to_typecast_expr(ex).op().type().id() == ID_bool){
      clean_o.insert(to_typecast_expr(ex).op());
    } else if(can_cast_expr<bounds_failuret>(ex)){
      auto toadd = typecast_exprt(ex, bool_typet());
      targetEquationt.merge_irep.merged1L(toadd);
      clean_bf.insert(to_bounds_failure(ex));
      clean_o.insert(toadd);
    } else {
      auto castop = typecast_exprt(ex, bool_typet());
      targetEquationt.merge_irep.merged1L(castop);
      clean_o.insert(castop);
    }
  }
  if(clean_o.empty()){
    auto ans = unsignedbv_typet(1).largest_expr();
    targetEquationt.merge_irep.merged1L(ans);
    return ans;
  } else if (clean_o.size() == 1){
    auto elem = *clean_o.begin();
    if(can_cast_expr<typecast_exprt>(elem) && to_typecast_expr(elem).op().type().id() == ID_bool)
      return to_typecast_expr(elem).op();
    else
    {
      auto ans = typecast_exprt::conditional_cast(elem, unsignedbv_typet(1));
      targetEquationt.merge_irep.merged1L(ans);
      return ans;
    }
  } else {
    std::vector<exprt> or_parts;
    for(const auto &bf: clean_bf){
      auto bfconv = typecast_exprt::conditional_cast(bf, bool_typet());
      targetEquationt.merge_irep.merged1L(bfconv);
      or_parts.push_back(bfconv);
    }
    for(const auto & op : clean_o){
      bool skip_this = false;
      if(
        can_cast_expr<typecast_exprt>(op) &&
        can_cast_expr<bounds_failuret>(to_typecast_expr(op).op()) &&
        clean_bf.count(to_bounds_failure(to_typecast_expr(op).op())))
      {
        skip_this = true;
        //break;
      } else if(auto an = expr_try_dynamic_cast<and_exprt>(op)){
        for(const auto &andel: an->operands()){
          if(can_cast_expr<typecast_exprt>(andel))
          {
            if(
              can_cast_expr<bounds_failuret>(to_typecast_expr(andel).op()) &&
              clean_bf.count(to_bounds_failure(to_typecast_expr(andel).op())))
            {
              skip_this = true;
              break;
            }
          }
        }
      }
      if(!skip_this)
      {
        auto opconv = typecast_exprt::conditional_cast(op, bool_typet());
        targetEquationt.merge_irep.merged1L(opconv);
        or_parts.push_back(opconv);
      }
    }
    PRECONDITION(!or_parts.empty());
    auto any = or_exprt(or_parts);
    targetEquationt.merge_irep.merged1L(any);
    auto ans = typecast_exprt::conditional_cast(any, unsignedbv_typet(1));
    targetEquationt.merge_irep.merged1L(ans);
    return ans;
  }
}

exprt bitor_simpl(symex_target_equationt &targetEquation,
                  const exprt &e0 = nil_exprt{},
                  const exprt &e1 = nil_exprt{}){
  std::vector<exprt> o;
  bool all_repl = true;
  if(!e0.is_nil() && !e0.is_zero()) o.push_back(e0);
  all_repl = all_repl && (o.empty() || can_cast_expr<replication_exprt>(o.back()));
  if(!e0.is_nil() && e0.is_one()) return e0;
  if(!e1.is_nil() && !e1.is_zero()) o.push_back(e1);
  all_repl = all_repl && (o.empty() || can_cast_expr<replication_exprt>(o.back()));
  if(!e1.is_nil() && e1.is_one()) return e1;
  if(o.empty())
    return e0;
  else if(o[0].type().id() == ID_unsignedbv && to_unsignedbv_type(o[0].type()).get_width() == 1){
    return bitor_simpl_onebit(targetEquation, o);
  }
  if(o.size() == 1)
    return o[0];
  else if(all_repl){
    auto or_inner = bitor_simpl(targetEquation, to_replication_expr(o[0]).op(), to_replication_expr(o[1]).op());
    auto ans = replication_exprt(to_replication_expr(o[0]).times(), or_inner, o[0].type());
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }
  else
  {
    bitor_exprt o01 = bitor_exprt(o[0], o[1]);
    targetEquation.merge_irep.merged1L(o01);
    return o01;
  }
}

exprt bitand_simpl_onebit(symex_target_equationt &targetEquationt,
                         std::vector<exprt> &o){
  std::vector<exprt> o_stack = o; //things to process, all unsigned{1}
  std::unordered_set<exprt, irep_hash> clean_o; //every expression is a boolean to be or-ed
  while(!o_stack.empty()){
    const exprt ex = o_stack.back();
    o_stack.pop_back();
    if(auto bito = expr_try_dynamic_cast<bitand_exprt>(ex)){
      o_stack.insert(o_stack.end(), bito->operands().begin(), bito->operands().end());
    } else if(can_cast_expr<typecast_exprt>(ex) && can_cast_expr<and_exprt>(to_typecast_expr(ex).op())){
      for(const auto &op : to_typecast_expr(ex).op().operands()){
        o_stack.push_back(typecast_exprt(op, unsignedbv_typet{1}));
        targetEquationt.merge_irep.merged1L(o_stack.back());
      }
    } else if(can_cast_expr<typecast_exprt>(ex) && to_typecast_expr(ex).op().type().id() == ID_bool){
      clean_o.insert(to_typecast_expr(ex).op());
    } else {
      auto ex_to_bool = typecast_exprt::conditional_cast(ex, bool_typet());
      targetEquationt.merge_irep.merged1L(ex_to_bool);
      clean_o.insert(ex_to_bool);
    }
  }
  if(clean_o.empty()){
    auto ans = unsignedbv_typet(1).smallest_expr();
    targetEquationt.merge_irep.merged1L(ans);
    return ans;
  } else if (clean_o.size() == 1){
    auto elem = *clean_o.begin();
    if(can_cast_expr<typecast_exprt>(elem) && to_typecast_expr(elem).op().type().id() == ID_unsignedbv)
      return to_typecast_expr(elem).op();
    else
    {
      auto ans = typecast_exprt::conditional_cast(elem, unsignedbv_typet(1));
      targetEquationt.merge_irep.merged1L(ans);
      return ans;
    }
  } else {
    std::vector<exprt> and_parts(clean_o.begin(), clean_o.end());
    auto all = and_exprt(and_parts);
    targetEquationt.merge_irep.merged1L(all);
    auto ans = typecast_exprt::conditional_cast(all, unsignedbv_typet(1));
    targetEquationt.merge_irep.merged1L(ans);
    return ans;
  }
}

exprt bitand_simpl(symex_target_equationt &targetEquation,
                   const exprt &e0 = nil_exprt{},
                  const exprt &e1 = nil_exprt{},
                  const exprt &e2 = nil_exprt{},
                  const exprt &e3 = nil_exprt{}){
  std::vector<exprt> o;
  if(!e0.is_nil() && !e0.is_one()) o.push_back(e0);
  if(!e0.is_nil() && e0.is_zero()) return e0;
  if(!e1.is_nil() && !e1.is_one()) o.push_back(e1);
  if(!e1.is_nil() && e1.is_zero()) return e1;
  if(!e2.is_nil() && !e2.is_one()) o.push_back(e2);
  if(!e2.is_nil() && e2.is_zero()) return e2;
  if(!e3.is_nil() && !e3.is_one()) o.push_back(e3);
  if(!e3.is_nil() && e3.is_zero()) return e3;
  if(o.empty())
    return e0;
  else if(o.size() == 1)
    return o[0];
  else if(o[0].type().id() == ID_unsignedbv && to_unsignedbv_type(o[0].type()).get_width() == 1){
    return bitand_simpl_onebit(targetEquation, o);
  }
  else if(o.size() == 2)
  {
    auto ans = bitand_exprt(o[0], o[1]);
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }
  else if(o.size() == 3)
  {
    auto ans = bitand_exprt(bitand_exprt(o[0], o[1]), o[2]);
    targetEquation.merge_irep.merged1L(ans.op0());
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }else
  {
    auto ans = bitand_exprt(bitand_exprt(o[0], o[1]), bitand_exprt(o[2], o[3]));
    targetEquation.merge_irep.merged1L(ans.op0());
    targetEquation.merge_irep.merged1L(ans.op1());
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }
}

exprt if_simpl(const exprt &cond, const exprt &then, const exprt &els, symex_target_equationt &targetEquation){
  if(then == els || cond.is_true())
    return then;
  else if(cond.is_false())
    return els;
  else if(then.is_zero() && can_cast_expr<replication_exprt>(els)){
    auto condbit = typecast_exprt(cond, unsignedbv_typet(1));
    targetEquation.merge_irep.merged1L(condbit);
    auto condelsbit = bitand_simpl(targetEquation, condbit, to_replication_expr(els).op());
    targetEquation.merge_irep.merged1L(condelsbit);
    auto ans = replication_exprt(to_replication_expr(els).times(), condelsbit, els.type());
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  } else {
    auto ans = if_exprt(cond, then, els);
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }
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

constant_exprt get_zero_sm_symbol(const typet &t, namespacet &ns, symex_target_equationt& targetEquation){
  auto ans = get_abs_type(t, ns).smallest_expr();
  targetEquation.merge_irep.merged1L(ans);
  return ans;
}
constant_exprt get_one_sm_symbol(const typet &t, namespacet &ns, symex_target_equationt& targetEquation){
  auto ans = get_abs_type(t, ns).largest_expr();
  targetEquation.merge_irep.merged1L(ans);
  return ans;
}

exprt get_abs_symbol(const ssa_exprt &orig, symex_target_equationt &targetEquation, namespacet &ns){
  /*if((*targetEquation.abs_exprs)[orig])
    return *(*targetEquation.abs_exprs)[orig];
  else*/
  {
    auto ident = as_string(orig.get_identifier());
    auto idx = ident.find_last_of("::");
    if(idx == std::string::npos)
      idx = 0;
    else
      idx += 2;
    auto abstr_ident = ident.substr(0,idx) + "__ABSTR__" + ident.substr(idx);
    return ssa_exprt(symbol_exprt(abstr_ident, get_abs_type(orig.type(), ns)));
  }
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
exprt update_sm(const exprt &bit, const typet &to_cover_tp, namespacet &ns, symex_target_equationt &targetEquation){
  PRECONDITION(can_cast_type<unsignedbv_typet>(bit.type()) && to_unsignedbv_type(bit.type()).get_width() == 1);
  auto to_cover_sm = get_abs_type(to_cover_tp, ns);
  if(auto const c = expr_try_dynamic_cast<constant_exprt>(bit)){
    constant_exprt ans = (c->is_zero())? unsignedbv_typet(to_cover_sm.get_width()).smallest_expr():unsignedbv_typet(to_cover_sm.get_width()).largest_expr();
    targetEquation.merge_irep.merged1L(ans);
    return ans;
  }
  auto repl_times = to_cover_sm.get_width();
  if(repl_times == 1)
    return bit;
  if(bit.id() == ID_reduction_or){
    const auto red = to_unary_expr(bit);
    if(const auto repl = expr_try_dynamic_cast<replication_exprt>(red.op())){
      auto ans = replication_exprt{
        from_integer(repl_times, size_type()), repl->op(), to_cover_sm};
      targetEquation.merge_irep.merged1L(ans.times());
      targetEquation.merge_irep.merged1L(ans);
      return ans;
    }
  }
  return replication_exprt{
    from_integer(repl_times, size_type()), bit, to_cover_sm};
}
exprt get_sm(const exprt &sm, symex_target_equationt& targetEquation){
  if(sm.is_constant()){
    auto cons = from_integer((sm.is_zero())?0:1, unsignedbv_typet(1));
    targetEquation.merge_irep.merged1L(cons);
    return cons;
  }
  if(sm.type().id() == ID_unsignedbv && to_unsignedbv_type(sm.type()).get_width() == 1){
    return sm;
  }
  if(const auto repl = expr_try_dynamic_cast<replication_exprt>(sm)){
    if(repl->op().type().id() == ID_unsignedbv && to_unsignedbv_type(repl->op().type()).get_width() == 1){
      return repl->op();
    } else {
      auto ans = unary_exprt{ID_reduction_or, repl->op(), unsignedbv_typet(1)};
      targetEquation.merge_irep.merged1L(ans);
      return ans;
    }
  }
  auto ans = unary_exprt{ID_reduction_or, sm, unsignedbv_typet(1)};
  targetEquation.merge_irep.merged1L(ans);
  return ans;
  //return typecast_exprt::conditional_cast(notequal_exprt{sm, to_unsignedbv_type(sm.type()).zero_expr()}, unsignedbv_typet(1));
}
/*exprt max_sm(const exprt &sm, const typet &to_cover_tp, namespacet &ns){
  auto bit = get_sm(sm);
  return update_sm(bit, to_cover_tp, ns);
}*/

inline bounds_failuret make_bf(const exprt &e, const size_t width, symex_target_equationt &targetEquation){
  auto bf = bounds_failuret(e, width);
  targetEquation.merge_irep.merged1L(bf);
  return bf;
}

exprt abstr_check(const exprt &e, bool abs_result, const size_t width, symex_target_equationt &targetEquation, namespacet &ns, boolbv_widtht &bv_width){
  exprt abs_check;
  // MARK ALL EXPRESSION GENERATED BY THIS FUNCTION AS "abstr_check_generated" AND "produce_no_abstract"
  // For expressions variable * constant, where variable is abstractable, even in the full representation, compute the tightest number of bits needed by mult: i.e, ignore the topmost equal literals.
  const auto map_key = std::make_pair(e, abs_result);
  if((*targetEquation.is_abstract)[map_key])
    return *(*targetEquation.is_abstract)[map_key];
  /*else if(!abs_result && (!(*targetEquation.produce_nonabs)[e] || !*(*targetEquation.produce_nonabs)[e])){
    PRECONDITION(false);
  } else if(abs_result && *(*targetEquation.is_abs_forbidden)[e]){
    PRECONDITION(false);
  }*/
  else if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(e)){
    bool has_sm = !*(*targetEquation.is_abs_forbidden)[e];
    bool needs_bounds_failure = abs_result && is_abstractable_type(ssa->type(), width, targetEquation);
    if(needs_bounds_failure)
      (*targetEquation.compute_bounds_failure)[e] = true;
    if(has_sm){
      if(needs_bounds_failure)
      {
        abs_check = update_sm(
          bitor_simpl(targetEquation,
                      get_sm(get_abs_symbol(*ssa, targetEquation, ns), targetEquation),
            make_bf(e, width, targetEquation)),
          ssa->type(),
          ns, targetEquation);
      } else
      {
        auto sym = get_abs_symbol(*ssa, targetEquation, ns);
        targetEquation.merge_irep.merged1L(sym);
        /*if((*(targetEquation.abs_guards_symbol))[sym].has_value()){
          abs_check = *((*(targetEquation.abs_guards_symbol))[sym]);
        } else {*/
          abs_check = sym;
        //}
      }
    } else {
      if(needs_bounds_failure)
        abs_check = update_sm(make_bf(e, width, targetEquation), ssa->type(), ns, targetEquation);
      else
        abs_check = get_zero_sm_symbol(ssa->type(), ns, targetEquation);
    }
  } else if (auto cons = expr_try_dynamic_cast<constant_exprt>(e)) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(cons->type(), width, targetEquation);
    if(needs_bounds_failure)
      (*targetEquation.compute_bounds_failure)[e] = true;
    /*if(needs_bounds_failure)
    {
      auto x = numeric_cast<mp_integer>(*cons);
      auto tp = to_integer_bitvector_type(cons->type()).smallest() < 0 ? (integer_bitvector_typet) signedbv_typet(width) : unsignedbv_typet(width);
      abs_check = (x < tp.smallest() || x > tp.largest())? get_one_sm_symbol(cons->type(), ns) : get_zero_sm_symbol(cons->type(), ns);
    } else {*/
    abs_check = get_zero_sm_symbol(cons->type(), ns, targetEquation);
    //}
  } else if (const auto nondet = expr_try_dynamic_cast<nondet_symbol_exprt>(e)) {
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
      (*targetEquation.compute_bounds_failure)[e] = true;
    /*if(needs_bounds_failure)
    {
      auto ndbit = get_random_bit(*nondet);
      abs_check = update_sm(ndbit, nondet->type(), ns);
    } else {*/
    abs_check = get_zero_sm_symbol(e.type(), ns, targetEquation);
    //}
  } else if (e.id() == ID_plus || e.id() == ID_minus || e.id() == ID_mult ||
          e.id() == ID_shl || e.id() == ID_div || e.id() == ID_rol ||
          e.id() == ID_ror || /*e.id() == ID_power ||*/ e.id() == ID_mod) {
    if(test_pattern_ptr_index_times_offset(e))
    {
      auto arr = e.operands()[0];
      auto idx = e.operands()[1].operands()[0];
      auto sz_elem = e.operands()[1].operands()[1];
      abs_check = update_sm(
        bitor_simpl(targetEquation,
                    get_sm(
            abstr_check(arr, abs_result, width, targetEquation, ns, bv_width), targetEquation),
          get_sm(
            abstr_check(idx, abs_result, width, targetEquation, ns, bv_width), targetEquation)),
        e.type(),
        ns, targetEquation);
    } else if(test_pattern_ptr_offset(e))
    {
      auto arr = e.operands()[0];
      auto offs = e.operands()[1];
      abs_check = abstr_check(arr, abs_result, width, targetEquation, ns, bv_width);
    } else if(test_pattern_ptroffset_const(e))
    {
      auto poff = e.operands()[0].is_constant() ? e.operands()[1] : e.operands()[0];
      abs_check = abstr_check(poff, abs_result, width, targetEquation, ns, bv_width);
    } else {
      bool needs_bounds_failure =
        abs_result && e.id() != ID_mod && is_abstractable_type(e.type(), width, targetEquation);
      if(needs_bounds_failure)
      {
        (*targetEquation.compute_bounds_failure)[e] = true;
      }
      auto op_ok = bitor_simpl(targetEquation,
                               get_sm(abstr_check(
          e.operands()[0], abs_result, width, targetEquation, ns, bv_width), targetEquation),
        get_sm(abstr_check(
          e.operands()[1], abs_result, width, targetEquation, ns, bv_width), targetEquation));
      for(size_t opidx = 2; opidx < e.operands().size(); opidx++){
        op_ok = bitor_simpl(targetEquation, op_ok,
          get_sm(abstr_check(
            e.operands()[opidx], abs_result, width, targetEquation, ns, bv_width), targetEquation));
      }
      if(needs_bounds_failure)
        op_ok = bitor_simpl(targetEquation, op_ok, make_bf(e, width, targetEquation));

      abs_check = update_sm(op_ok, e.type(), ns, targetEquation);
    }
  } else if (e.id() == ID_ge || e.id() == ID_gt || e.id() == ID_le ||
          e.id() == ID_lt || e.id() == ID_equal || e.id() == ID_notequal) {
    bool do_operands_with_abstraction = abs_result && can_abstract(e.operands(), targetEquation);
    if(!do_operands_with_abstraction)
      assert(*(*targetEquation.produce_nonabs)[e]);
    auto op_ok = bitor_simpl(targetEquation, get_sm(abstr_check(e.operands()[0], do_operands_with_abstraction, width, targetEquation, ns, bv_width), targetEquation),
                             get_sm(abstr_check(e.operands()[1], do_operands_with_abstraction, width, targetEquation, ns, bv_width), targetEquation));
    abs_check = op_ok;//update_sm(op_ok, e.type(), ns);
  } else if (const auto be = expr_try_dynamic_cast<byte_extract_exprt>(e)) {
    // see if you can restrict the offset search somehow (e.g., offset is limited to x bits)
    // maybe, have a look on the higher literals of offset
    exprt offset_abs = get_sm(abstr_check(be->offset(), abs_result, width, targetEquation, ns, bv_width), targetEquation);
    exprt op_sm = abstr_check(be->op(), abs_result, width, targetEquation, ns, bv_width);
    exprt extract_op_sm;
    if(op_sm.is_zero())
      extract_op_sm = get_zero_sm_symbol(be->type(), ns, targetEquation);
    else
    {
      extract_op_sm = byte_extract_exprt(
        ID_byte_extract_little_endian,
        op_sm,
        be->offset(),
        1,
        get_abs_type(be->type(), ns));
      targetEquation.merge_irep.merged1L(extract_op_sm);
    }
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_simpl(targetEquation, update_sm(bitor_simpl(targetEquation, make_bf(e, width, targetEquation), offset_abs), e.type(), ns, targetEquation), extract_op_sm);
    } else {
      abs_check = bitor_simpl(targetEquation, update_sm(offset_abs, e.type(), ns, targetEquation), extract_op_sm);
    }
  } else if (const auto eb = expr_try_dynamic_cast<extractbits_exprt>(e)) {
    auto const maybe_upper_as_int = numeric_cast<mp_integer>(eb->upper());
    auto const maybe_lower_as_int = numeric_cast<mp_integer>(eb->lower());
    auto const lower_byte = (*maybe_lower_as_int/8).to_long();
    auto const upper_byte = ((*maybe_upper_as_int+6)/8).to_long(); //ceil((*maybe_upper_as_int-1)/8)
    exprt op_sm = abstr_check(eb->src(), abs_result, width, targetEquation, ns, bv_width);
    auto extract_op_sm = extractbits_exprt(op_sm, upper_byte, lower_byte, unsignedbv_typet(upper_byte - lower_byte + 1));
    targetEquation.merge_irep.merged1L(extract_op_sm);
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_simpl(targetEquation, update_sm(make_bf(e, width, targetEquation), extract_op_sm.type(), ns, targetEquation), extract_op_sm);
    } else {
      abs_check = extract_op_sm;
    }
  } else if (const auto ebit = expr_try_dynamic_cast<extractbit_exprt>(e)) {
    auto const maybe_index_as_int = numeric_cast<mp_integer>(ebit->index());
    auto const index_byte = (*maybe_index_as_int/8).to_long();
    exprt op_sm = abstr_check(ebit->src(), abs_result, width, targetEquation, ns, bv_width);
    auto extract_op_sm = extractbit_exprt(op_sm, index_byte);
    targetEquation.merge_irep.merged1L(extract_op_sm);
    bool needs_bounds_failure = abs_result && is_abstractable_type(e.type(), width, targetEquation);
    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = bitor_simpl(targetEquation, update_sm(make_bf(e, width, targetEquation), extract_op_sm.type(), ns, targetEquation), extract_op_sm);
    } else {
      abs_check = extract_op_sm;
    }
  } else if (const auto bu = expr_try_dynamic_cast<byte_update_exprt>(e)) {
    // see if you can restrict the offset search somehow (e.g., offset is limited to x bits)
    // maybe, have a look on the higher literals of offset
    exprt offset_abs = get_sm(abstr_check(bu->offset(), abs_result, width, targetEquation, ns, bv_width), targetEquation);
    exprt op_sm = abstr_check(bu->op(), abs_result, width, targetEquation, ns, bv_width);
    exprt value_sm = abstr_check(bu->value(), abs_result, width, targetEquation, ns, bv_width);
    if(op_sm.is_nil() || offset_abs.is_nil() || value_sm.is_nil())
      abs_check.make_nil();
    else
    {
      /*bool needs_bounds_failure =
        abs_result && is_abstractable_type(e.type(), width, targetEquation);*/
      auto bupdate_sm = byte_update_exprt(
        ID_byte_update_little_endian, op_sm, bu->offset(), value_sm, 1);
      targetEquation.merge_irep.merged1L(bupdate_sm);
      /*if(needs_bounds_failure)
      {
        UNREACHABLE;
        / *(*targetEquation.compute_bounds_failure)[e] = true;
        abs_check = bitor_exprt(
          update_sm(
            bitor_exprt(bounds_failuret(*bu, width), offset_abs),
            e.type(),
            ns),
          bupdate_sm);* /
      }
      else*/
      {
        abs_check =
          bitor_simpl(targetEquation, update_sm(offset_abs, e.type(), ns, targetEquation), bupdate_sm);
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
      abs_check = bitor_simpl(targetEquation, then_abs, else_abs);//if_simpl(ife->cond(), then_abs, else_abs, targetEquation);
      if(!cond_abs_bits.is_false()){
        abs_check = bitor_simpl(targetEquation, update_sm(get_sm(cond_abs_bits, targetEquation), ife->type(), ns, targetEquation), abs_check);
      }
    }
  } else if (const auto ae = expr_try_dynamic_cast<and_exprt>(e))
  {
    //(foreach i: ci is not sound or ci is true) and (exists i: ci is not sound)
    //exprt foreach_not_sound_or_true = get_one_sm_symbol(unsigned_char_type(), ns);
    exprt exists_unsound = get_zero_sm_symbol(unsigned_char_type(), ns, targetEquation);
    bool first = true;
    for(const auto &op: ae->operands()){
      exprt check = abstr_check(op, can_abstract(op, targetEquation), width, targetEquation, ns, bv_width);
      if(first){
        //foreach_not_sound_or_true = bitor_simpl(check, typecast_exprt::conditional_cast(op, unsignedbv_typet(1)));
        exists_unsound = check;
        first = false;
      } else {
        //foreach_not_sound_or_true = bitand_simpl(foreach_not_sound_or_true, bitor_simpl(check, typecast_exprt::conditional_cast(op, unsignedbv_typet(1))));
        exists_unsound = bitor_simpl(targetEquation, exists_unsound, check);
      }
    }
    abs_check = exists_unsound;//bitand_simpl(foreach_not_sound_or_true, exists_unsound);
  } else if (const auto oe = expr_try_dynamic_cast<or_exprt>(e))
  {
    //(foreach i: ci is not sound or ci is false) and (exists i: ci is not sound)
    exprt foreach_not_sound_or_false = get_one_sm_symbol(unsigned_char_type(), ns, targetEquation);
    exprt exists_unsound = get_zero_sm_symbol(unsigned_char_type(), ns, targetEquation);
    bool first = true;
    for(const auto &op: oe->operands()){
      exprt check = abstr_check(op, can_abstract(op, targetEquation), width, targetEquation, ns, bv_width);
      auto op_to_bit = typecast_exprt::conditional_cast(op, unsignedbv_typet(1));
      targetEquation.merge_irep.merged1L(op_to_bit);
      auto op_is_false = bitnot_exprt(op_to_bit);
      targetEquation.merge_irep.merged1L(op_is_false);
      //auto op_not_sound_or_false = bitor_simpl(targetEquation, check, op_is_false);
      //targetEquation.merge_irep.merged1L(op_not_sound_or_false);
      if(first){

        //foreach_not_sound_or_false = op_not_sound_or_false;
        exists_unsound = check;
        first = false;
      } else {
        //foreach_not_sound_or_false = bitand_simpl(targetEquation, foreach_not_sound_or_false, op_not_sound_or_false);
        exists_unsound = bitor_simpl(targetEquation, exists_unsound, check);
      }
    }
    abs_check = exists_unsound;//bitand_simpl(foreach_not_sound_or_false, exists_unsound);
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
    targetEquation.merge_irep.merged1L(A);
    targetEquation.merge_irep.merged1L(B);

    abs_check = //bitand_simpl(
      bitor_simpl(targetEquation, checkA, checkB)//,
      /*bitand_simpl(
        bitor_simpl(checkB, bitnot_exprt(B)),
        bitor_simpl(checkA, A)))*/;
  } else if (const auto cast = expr_try_dynamic_cast<typecast_exprt>(e))
  {
    bool needs_bounds_failure =
      abs_result && is_abstractable_type(e.type(), width, targetEquation);
    auto op_check = (get_sm(abstr_check(cast->op(), abs_result, width, targetEquation, ns, bv_width), targetEquation));

    if(needs_bounds_failure)
    {
      (*targetEquation.compute_bounds_failure)[e] = true;
      abs_check = update_sm(
        bitor_simpl(targetEquation, op_check, make_bf(e, width, targetEquation)),
          cast->type(),
          ns, targetEquation);
    }
    else
    {
      abs_check = update_sm(
        op_check,
        cast->type(),
        ns, targetEquation);
    }
  } else if (const auto str = expr_try_dynamic_cast<struct_exprt>(e)) {
    exprt::operandst elems;
    bool all_zeros = true;
    auto op_it=str->operands().begin();
    size_t bitIdx = 0;
    while(op_it != str->operands().end()){
      const auto& op = *op_it;
      size_t sz = bv_width(op.type());
      auto op_ab = abstr_check(op, abs_result, width, targetEquation, ns, bv_width);
      all_zeros = all_zeros && op_ab.is_zero();
      if(bitIdx % 8 == 0){ // start from a complete byte
        elems.push_back(op_ab);
      } else if (sz == 8-(bitIdx % 8)) {
        // pad to reach the nearest byte, just or with the latest byte
        if(!op_ab.is_zero()){
          auto last_elem_sm = elems.back();
          auto last_op_sm_sz = bv_width(last_elem_sm.type());
          if(last_op_sm_sz > 1)
          {
            //more than 1 byte, just or the last byte
            auto last_elem_without_last_byte = extractbits_exprt(
              last_elem_sm,
              last_op_sm_sz - 2,
              0,
              unsignedbv_typet(last_op_sm_sz - 1));
            targetEquation.merge_irep.merged1L(last_elem_without_last_byte);
            auto extr_last_byte = extractbit_exprt(
              *elems.rbegin(),
              last_op_sm_sz - 1);
            targetEquation.merge_irep.merged1L(extr_last_byte);
            auto last_byte = bitor_simpl(targetEquation, extr_last_byte, op_ab);
            targetEquation.merge_irep.merged1L(last_byte);
            elems.pop_back();
            elems.push_back(last_elem_without_last_byte);
            elems.push_back(last_byte);

          } else {
            // 1 byte, or the whole last element
            auto last_byte = bitor_simpl(targetEquation, last_elem_sm, op_ab);
            elems.pop_back();
            elems.push_back(last_byte);
          }
        }
      } else {
        // grab what's left from the incomplete byte and or with the first byte of the new abs, then add the new element's abs taking care of the bits "missing"
        UNIMPLEMENTED;
      }
      //abs_check = byte_update_exprt(ID_byte_update_little_endian, abs_check, from_integer(bitIdx/8, size_type()), op_ab, 1);
      bitIdx += sz;
      op_it++;
    }
    abs_check = all_zeros ? (exprt) get_zero_sm_symbol(e.type(), ns, targetEquation) : concatenation_exprt(elems, get_abs_type(e.type(), ns));
    targetEquation.merge_irep.merged1L(abs_check);
  } /*else if (const auto str = expr_try_dynamic_cast<struct_exprt>(e))
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
  }*/
  else if (const auto aof = expr_try_dynamic_cast<array_of_exprt>(e))
  {
    const auto array_smtype = get_abs_type(e.type(), ns);
    const auto elem_smtype = get_abs_type(aof->what().type(), ns);
    const auto copies = array_smtype.get_width()/std::max((size_t)1, elem_smtype.get_width());
    const auto elem_sm = abstr_check(aof->what(), abs_result, width, targetEquation, ns, bv_width);
    abs_check = replication_exprt(from_integer(copies, size_type()), elem_sm, array_smtype);
    targetEquation.merge_irep.merged1L(abs_check.operands()[0]);
    targetEquation.merge_irep.merged1L(abs_check);
  } else if (const auto idx = expr_try_dynamic_cast<index_exprt>(e))
  {
    const auto idx_sm = get_sm(abstr_check(
      idx->index(),
      can_abstract(idx->index(), targetEquation),
      width,
      targetEquation,
      ns,
      bv_width), targetEquation);
    const auto array_sm = get_sm(abstr_check(
      idx->array(), abs_result, width, targetEquation, ns, bv_width), targetEquation);
    const auto elem_smtype = get_abs_type(idx->type(), ns);
    const auto elem_width =
      from_integer(elem_smtype.get_width(), idx->index().type());
    targetEquation.merge_irep.merged1L(elem_width);
    exprt elem_sm;
    if(array_sm.is_zero()){
      elem_sm = get_zero_sm_symbol(idx->type(), ns, targetEquation);
    } else {
      auto elem_offset = mult_exprt(elem_width, idx->index());
      targetEquation.merge_irep.merged1L(elem_offset);
      elem_sm = byte_extract_exprt(
        ID_byte_extract_little_endian,
        array_sm,
        elem_offset,
        1,
        elem_smtype);
      targetEquation.merge_irep.merged1L(elem_sm);
    }
    abs_check = bitor_simpl(targetEquation,
                            elem_sm,
      update_sm(idx_sm, idx->type(), ns, targetEquation));
  } else if (const auto poff = expr_try_dynamic_cast<pointer_offset_exprt>(e))
  {
    const auto ptr_sm = get_sm(abstr_check(
      poff->pointer(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width), targetEquation);
    abs_check = update_sm(ptr_sm, poff->type(), ns, targetEquation);
  } else if (const auto pobj = expr_try_dynamic_cast<pointer_object_exprt>(e))
  {
    const auto ptr_sm = get_sm(abstr_check(
      pobj->pointer(),
      abs_result,
      width,
      targetEquation,
      ns,
      bv_width), targetEquation);
    abs_check = update_sm(ptr_sm, pobj->type(), ns, targetEquation);
  } else if (const auto arr = expr_try_dynamic_cast<array_exprt>(e))
  {
    std::vector<exprt> elems_sm;
    for(const auto &op: arr->operands()){
      elems_sm.push_back(abstr_check(op, abs_result, width, targetEquation, ns, bv_width));
    }
    abs_check = concatenation_exprt(elems_sm, get_abs_type(arr->type(), ns));
    targetEquation.merge_irep.merged1L(abs_check);
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
      bv_width), targetEquation), with->old().type(), ns, targetEquation);
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
        targetEquation.merge_irep.merged1L(old_sm_index.op0());
        targetEquation.merge_irep.merged1L(old_sm_index.op1());
        targetEquation.merge_irep.merged1L(old_sm_index);
        auto overwrite_arr_sm = byte_update_exprt(
          ID_byte_update_little_endian, old_sm, old_sm_index, new_sm, 1);
        targetEquation.merge_irep.merged1L(overwrite_arr_sm);
        abs_check = bitor_simpl(targetEquation, overwrite_arr_sm, where_sm_extended);
      }
      else
      {
        auto old_sm_index = mult_exprt(
          with->where(), from_integer(new_sm_width, with->where().type()));
        targetEquation.merge_irep.merged1L(old_sm_index.op1());
        targetEquation.merge_irep.merged1L(old_sm_index);
        auto overwrite_arr_sm = byte_update_exprt(
          ID_byte_update_little_endian, old_sm, old_sm_index, new_sm, 1);
        targetEquation.merge_irep.merged1L(overwrite_arr_sm);
        abs_check = bitor_simpl(targetEquation,
                                overwrite_arr_sm,
          where_sm_extended);
      }
    } else {
      UNIMPLEMENTED;
    }
    abs_check = bitor_simpl(targetEquation, where_sm_extended, abs_check);
  } else if (const auto aoff = expr_try_dynamic_cast<address_of_exprt>(e))
  {
    abs_check = get_zero_sm_symbol(aoff->type(), ns, targetEquation);
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
      //, targetEquation
      if(op_ab.is_zero()){
        abs_check = get_zero_sm_symbol(member->op().type(), ns, targetEquation);
      } else {
        auto offs_member = from_integer(member_bits.offset/8, unsigned_int_type());
        targetEquation.merge_irep.merged1L(offs_member);
        abs_check = byte_extract_exprt(ID_byte_extract_little_endian, op_ab, offs_member, 1, get_abs_type(e.type(), ns));
        targetEquation.merge_irep.merged1L(abs_check);
      }
    } else {
      UNIMPLEMENTED;
    }
  } else {
    UNIMPLEMENTED;
    abs_check.make_nil();
  }
  assert((to_integer_bitvector_type(abs_check.type()).get_width() == get_abs_type(e.type(), ns).get_width()));
  //targetEquation.merge_irep.merged1L(abs_check);
  //produce_nonabs(abs_check, targetEquation);
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

exprt abstr_guard(symex_target_equationt &targetEquation, const exprt &e){
  auto search = (*targetEquation.abs_guards_symbol)[e];
  if(search.has_value())
    return *search;
  PRECONDITION(!expr_try_dynamic_cast<ssa_exprt>(e));
  if(auto nt = expr_try_dynamic_cast<not_exprt>(e)){
    (*targetEquation.abs_guards_symbol)[e] = abstr_guard(targetEquation, nt->op());
  } else if(can_cast_expr<and_exprt>(e) || can_cast_expr<or_exprt>(e)){
    exprt op_abstr = abstr_guard(targetEquation, e.operands()[0]);
    for(size_t i=1; i<e.operands().size(); i++)
      op_abstr = bitor_simpl(targetEquation, op_abstr, abstr_guard(targetEquation, e.operands()[i]));
    (*targetEquation.abs_guards_symbol)[e] = op_abstr;
  } else if(e.is_constant()) {
    (*targetEquation.abs_guards_symbol)[e] = unsignedbv_typet(1).zero_expr();
  } else {
    UNREACHABLE;
  }
  return *(*targetEquation.abs_guards_symbol)[e];
}

void apply_cut(symex_target_equationt &targetEquation, namespacet &ns){
  targetEquation.is_abs_forbidden = {std::map<exprt,optionalt<bool>>()};
  targetEquation.produce_nonabs = {std::map<exprt,optionalt<bool>>()};
  for(SSA_stept &step:targetEquation.SSA_steps)
  {
    if(!step.ignore){
      switch(step.type)
      {
      case goto_trace_stept::typet::ASSIGNMENT:
      {
        bool lhs_abs_forbidden = set_if_abs_forbidden(step.ssa_lhs, targetEquation);
        set_if_abs_forbidden(step.ssa_rhs, targetEquation);
        set_if_abs_forbidden(step.guard, targetEquation);
        if(lhs_abs_forbidden)
        {
          produce_nonabs(step.ssa_lhs, targetEquation);
          produce_nonabs(step.ssa_rhs, targetEquation);
        }
        break ;
      }
      case goto_trace_stept::typet::ASSERT:
      case goto_trace_stept::typet::ASSUME:
      {
        set_if_abs_forbidden(step.cond_expr, targetEquation);
        break;
      }
      case goto_trace_stept::typet::NONE:
      case goto_trace_stept::typet::GOTO:
      case goto_trace_stept::typet::LOCATION:
      case goto_trace_stept::typet::INPUT:
      case goto_trace_stept::typet::OUTPUT:
      case goto_trace_stept::typet::DECL:
      case goto_trace_stept::typet::DEAD:
      case goto_trace_stept::typet::FUNCTION_CALL:
      case goto_trace_stept::typet::FUNCTION_RETURN:
      case goto_trace_stept::typet::CONSTRAINT:
      case goto_trace_stept::typet::SHARED_READ:
      case goto_trace_stept::typet::SHARED_WRITE:
      case goto_trace_stept::typet::SPAWN:
      case goto_trace_stept::typet::MEMORY_BARRIER:
      case goto_trace_stept::typet::ATOMIC_BEGIN:
      case goto_trace_stept::typet::ATOMIC_END:
        break;
      }
    }
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
  targetEquation.abs_exprs = {std::map<ssa_exprt,optionalt<exprt>>()};
  targetEquation.is_assigned = {std::map<exprt,optionalt<bool>>()};
  targetEquation.abs_guards_symbol = {std::map<exprt,optionalt<exprt>>()};
  for(SSA_stept &step:targetEquation.SSA_steps){
    if(step.ignore)
      abs_steps.emplace_back(step);
    else {
    set_if_abs_forbidden(step.guard, targetEquation);
    switch(step.type)
    {
    case goto_trace_stept::typet::NONE:
      abs_steps.emplace_back(step);
      break;
    case goto_trace_stept::typet::ASSIGNMENT:{
      abs_steps.emplace_back(step);
      bool lhs_abs_forbidden = set_if_abs_forbidden(step.ssa_lhs, targetEquation);
      set_if_abs_forbidden(step.ssa_rhs, targetEquation);
      set_if_abs_forbidden(step.guard, targetEquation);
      (*targetEquation.is_assigned)[step.ssa_rhs] = true;
      if(lhs_abs_forbidden)
      {
        produce_nonabs(step.ssa_lhs, targetEquation);
        produce_nonabs(step.ssa_rhs, targetEquation);
      }
      if(!lhs_abs_forbidden)
      {
        ssa_exprt abstr_lhs = to_ssa_expr(get_abs_symbol(step.ssa_lhs, targetEquation, ns));
        auto abstr_rhs = abstr_check(
          step.ssa_rhs, !lhs_abs_forbidden, width, targetEquation, ns, bv_width);
#if 0
        auto abstr_guard = abstr_check(
          step.guard, true, width, targetEquation, ns, bv_width);
        PRECONDITION(can_cast_type<unsignedbv_typet>(abstr_guard.type()) && to_unsignedbv_type(abstr_guard.type()).get_width() == 1);

        exprt guard_evals_to_true;

        if(!abstr_guard.is_zero())
        {
          abs_steps.emplace_back(SSA_assignment_stept{
            step.source,
            abstr_guard,
            abstr_lhs,
            nil_exprt(),
            nil_exprt(),
            get_one_sm_symbol(step.ssa_lhs.type(), ns),
            step.assignment_type});
          targetEquation.merge_ireps(abs_steps.back());
          guard_evals_to_true = typecast_exprt::conditional_cast(bitand_simpl(bitnot_exprt(abstr_guard), typecast_exprt::conditional_cast(step.guard, unsignedbv_typet(1))), bool_typet());
        } else {
          guard_evals_to_true = step.guard;
        }

        abs_steps.emplace_back(SSA_assignment_stept{
          step.source,
          guard_evals_to_true,
          abstr_lhs,
          nil_exprt(),
          nil_exprt(),
          abstr_rhs,
          step.assignment_type});
        targetEquation.merge_ireps(abs_steps.back());

        if(step.assignment_type == symex_target_equationt::assignment_typet::GUARD && guard_evals_to_true.is_true() && (abstr_rhs.is_one() || abstr_rhs.is_zero()))
        {
          (*targetEquation.abs_guards_symbol)[abstr_lhs] = abstr_rhs;
        }

#else
#ifndef DISABLEABS
        exprt abstr_val;
        exprt abstr_val_if_ok;
        if(step.guard.is_true())
        {
            abstr_val_if_ok = abstr_rhs;
        } else if (step.guard.is_false())
        {
            abstr_val_if_ok = get_zero_sm_symbol(step.ssa_lhs.type(), ns, targetEquation);
        } else
        {
            abstr_val_if_ok = if_simpl(step.guard, abstr_rhs, get_zero_sm_symbol(step.ssa_lhs.type(), ns, targetEquation), targetEquation);
        }
        auto is_guard_abs = abstr_guard(targetEquation, step.guard);
        if(is_guard_abs.is_zero())
        {
            abstr_val = abstr_val_if_ok;
        } else if (is_guard_abs.is_one())
        {
            abstr_val = get_one_sm_symbol(step.ssa_lhs.type(), ns, targetEquation);
        } else
        {
            abstr_val = if_simpl(typecast_exprt::conditional_cast(abstr_guard(targetEquation, step.guard), bool_typet()), get_one_sm_symbol(step.ssa_lhs.type(), ns, targetEquation), abstr_val_if_ok, targetEquation);
        }
        abstr_val = abstr_rhs; /////////////////

        //targetEquation.merge_irep(abstr_rhs);
        if(step.assignment_type == symex_target_equationt::assignment_typet::GUARD)// && step.guard.is_true() && (abstr_rhs.is_one() || abstr_rhs.is_zero()))
        {
          (*targetEquation.abs_guards_symbol)[step.ssa_lhs] = abstr_rhs;
        }
        if(can_cast_expr<ssa_exprt>(abstr_val))
          (*targetEquation.abs_exprs)[step.ssa_lhs] = to_ssa_expr(abstr_val);
        else
        {
          /*abs_steps.emplace_back(SSA_assignment_stept{
          step.source,
          true_exprt(),
          abstr_lhs,
          nil_exprt(),
          nil_exprt(),
          abstr_val,
          step.assignment_type});
          targetEquation.merge_ireps(abs_steps.back());*/
        }
        (*targetEquation.abs_exprs)[step.ssa_lhs] = (abstr_val);
#endif
#endif
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
    {
      set_if_abs_forbidden(step.cond_expr, targetEquation);
      /*exprt abs_ok = equal_exprt{
        abstr_check(step.cond_expr, true, width, targetEquation, ns, bv_width),
        unsignedbv_typet{1}.zero_expr()};
      targetEquation.merge_irep.merged1L(abs_ok);
      step.cond_expr = and_exprt{
        step.cond_expr,
        abs_ok};*/
      abs_steps.emplace_back(step);
      targetEquation.merge_irep.merged1L(step.cond_expr);
      break;
    }case goto_trace_stept::typet::ASSERT:
    {
      set_if_abs_forbidden(step.cond_expr, targetEquation);
      /*exprt abs_notok = notequal_exprt{
        abstr_check(step.cond_expr, true, width, targetEquation, ns, bv_width),
        unsignedbv_typet{1}.zero_expr()};
      targetEquation.merge_irep.merged1L(abs_notok);
      step.cond_expr = or_exprt{
        step.cond_expr,
        abs_notok};*/
      abs_steps.emplace_back(step);
      targetEquation.merge_irep.merged1L(step.cond_expr);
      //TODO: assume(abs_ok) puo' fare bene?
      break;
    }
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