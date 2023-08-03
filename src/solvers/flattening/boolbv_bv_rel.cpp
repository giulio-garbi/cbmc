/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/bitvector_types.h>

#include <solvers/floatbv/float_utils.h>

#include "arith_tools.h"
#include "boolbv.h"
#include "boolbv_type.h"

optionalt<literalt> try_simplified_check(const bool sign, const constant_exprt& lhs, const dstringt& cmp, const int rhs_bits){
  mp_integer val_lhs;
  if(!to_integer(to_constant_expr(lhs), val_lhs))
  {
    mp_integer rhs_lowerbound;
    mp_integer rhs_upperbound;
    if(sign)
    {
      rhs_lowerbound = -power(2, rhs_bits - 1);
      rhs_upperbound = power(2, rhs_bits - 1) - 1;
    }
    else
    {
      rhs_lowerbound = 0;
      rhs_upperbound = power(2, rhs_bits) - 1;
    }
    if(cmp == ID_ge){
      if(val_lhs >= rhs_upperbound)
        return {const_literal(true)};
      else if(val_lhs < rhs_lowerbound)
        return {const_literal(false)};
      else
        return {};
    }
    else if(cmp == ID_gt){
      if(val_lhs > rhs_upperbound)
        return {const_literal(true)};
      else if(val_lhs <= rhs_lowerbound)
        return {const_literal(false)};
      else
        return {};
    }
    else if(cmp == ID_le){
      if(val_lhs > rhs_upperbound)
        return {const_literal(false)};
      else if(val_lhs <= rhs_lowerbound)
        return {const_literal(true)};
      else
        return {};
    }
    else if(cmp == ID_lt){
      if(val_lhs >= rhs_upperbound)
        return {const_literal(false)};
      else if(val_lhs < rhs_lowerbound)
        return {const_literal(true)};
      else
        return {};
    }
  }
  return {};
}

inline dstringt invert(const dstringt& cmp){
  if(cmp == ID_ge)
    return ID_lt;
  else if(cmp == ID_gt)
    return ID_le;
  else if(cmp == ID_le)
    return ID_gt;
  else if(cmp == ID_lt)
    return ID_ge;
  else
    return cmp;
}

/// Flatten <, >, <= and >= expressions.
literalt boolbvt::convert_bv_rel(const binary_relation_exprt &expr)
{
  const irep_idt &rel=expr.id();

  const exprt &lhs = expr.lhs();
  const exprt &rhs = expr.rhs();

  bvt bv_lhs = convert_bv(lhs);
  bvt bv_rhs = convert_bv(rhs);

  bvtypet bvtype_lhs = get_bvtype(lhs.type());
  bvtypet bvtype_rhs = get_bvtype(rhs.type());

  if(
    bv_lhs.size() == bv_rhs.size() && !bv_lhs.empty() &&
    bvtype_lhs == bvtype_rhs)
  {
    if(bvtype_lhs == bvtypet::IS_FLOAT)
    {
      float_utilst float_utils(prop, to_floatbv_type(lhs.type()));

      if(rel == ID_le)
        return float_utils.relation(bv_lhs, float_utilst::relt::LE, bv_rhs);
      else if(rel == ID_lt)
        return float_utils.relation(bv_lhs, float_utilst::relt::LT, bv_rhs);
      else if(rel == ID_ge)
        return float_utils.relation(bv_lhs, float_utilst::relt::GE, bv_rhs);
      else if(rel == ID_gt)
        return float_utils.relation(bv_lhs, float_utilst::relt::GT, bv_rhs);
      else
        return SUB::convert_rest(expr);
    }
    else if(
      (lhs.type().id() == ID_range && rhs.type() == lhs.type()) ||
      bvtype_lhs == bvtypet::IS_SIGNED || bvtype_lhs == bvtypet::IS_UNSIGNED ||
      bvtype_lhs == bvtypet::IS_FIXED)
    {
      literalt literal;

      bv_utilst::representationt rep = ((bvtype_lhs == bvtypet::IS_SIGNED) ||
                                        (bvtype_lhs == bvtypet::IS_FIXED))
                                         ? bv_utilst::representationt::SIGNED
                                         : bv_utilst::representationt::UNSIGNED;

#if 1
      if(!produce_nonabs(expr) && bv_lhs.size() > (size_t)*abstraction_bits && (bvtype_lhs == bvtypet::IS_SIGNED || bvtype_lhs == bvtypet::IS_UNSIGNED)) {
        bv_lhs.resize(*abstraction_bits);
        bv_rhs.resize(*abstraction_bits);
      }
      if(bvtype_lhs == bvtypet::IS_SIGNED || bvtype_lhs == bvtypet::IS_UNSIGNED){
        auto lhs_bits = bv_utils.how_many_bits(rep, bv_lhs);
        auto rhs_bits = bv_utils.how_many_bits(rep, bv_rhs);
        if(lhs.is_constant())
        {
          if(lhs.is_zero() && bvtype_lhs == bvtypet::IS_SIGNED){
            if(expr.id() == ID_gt)
              return bv_rhs.back();
            else if(expr.id() == ID_le)
              return neg(bv_rhs.back());
          }
          auto const_test = try_simplified_check(
            bvtype_lhs == bvtypet::IS_SIGNED,
            to_constant_expr(lhs),
            expr.id(),
            rhs_bits);
          if(const_test)
            return *const_test;
        }
        if(rhs.is_constant())
        {
          if(rhs.is_zero() && bvtype_lhs == bvtypet::IS_SIGNED){
            if(expr.id() == ID_lt)
              return bv_lhs.back();
            else if(expr.id() == ID_ge)
              return neg(bv_lhs.back());
          }
          auto const_test = try_simplified_check(
            bvtype_lhs == bvtypet::IS_SIGNED,
            to_constant_expr(rhs),
            invert(expr.id()),
            lhs_bits);
          if(const_test)
            return *const_test;
        }
        auto bits = std::max(lhs_bits, rhs_bits);
        bv_lhs.resize(bits);
        bv_rhs.resize(bits);
      }
      return bv_utils.rel(bv_lhs, expr.id(), bv_rhs, rep);

#else
      literalt literal = bv_utils.rel(bv_lhs, expr.id(), bv_rhs, rep);

      if(prop.has_set_to())
      {
        // it's unclear if this helps
        if(bv_lhs.size() > 8)
        {
          literalt equal_lit = equality(lhs, rhs);

          if(or_equal)
            prop.l_set_to_true(prop.limplies(equal_lit, literal));
          else
            prop.l_set_to_true(prop.limplies(equal_lit, !literal));
        }
      }

      return literal;
#endif
    }
    else if(
      (bvtype_lhs == bvtypet::IS_VERILOG_SIGNED ||
       bvtype_lhs == bvtypet::IS_VERILOG_UNSIGNED) &&
      lhs.type() == rhs.type())
    {
      // extract number bits
      bvt extract0, extract1;

      extract0.resize(bv_lhs.size() / 2);
      extract1.resize(bv_rhs.size() / 2);

      for(std::size_t i = 0; i < extract0.size(); i++)
        extract0[i] = bv_lhs[i * 2];

      for(std::size_t i = 0; i < extract1.size(); i++)
        extract1[i] = bv_rhs[i * 2];

      bv_utilst::representationt rep = bv_utilst::representationt::UNSIGNED;

      // now compare
      return bv_utils.rel(extract0, expr.id(), extract1, rep);
    }
  }

  return SUB::convert_rest(expr);
}
