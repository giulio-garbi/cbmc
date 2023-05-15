/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/byte_operators.h>
#include <util/invariant.h>
#include <util/std_expr.h>

#include "bitvector_types.h"
#include "boolbv.h"
#include "cprover_prefix.h"
#include "ssa_expr.h"

bool boolbvt::keep_all_bits(const typet &tp, std::vector<bool> &bitmap, const int from, const int to){
  if(!abstraction_bits)
    return true;
  if(tp.get_string(ID_C_typedef) == "__cs_mutex_t")
    return true;
  size_t ab_width = *abstraction_bits;
  if(const auto ibt = type_try_dynamic_cast<integer_bitvector_typet>(tp)){
    if(ibt->get_width() > ab_width){
      for(int i = from+ab_width; i < to; i++)
        bitmap[i] = false;
      return false;
    }
  }
  else if(const auto str = type_try_dynamic_cast<struct_typet>(tp)){
    bool no_cuts = true;
    for(const auto &f: str->components()){
      const auto f_width = bv_width.get_member(*str,f.get_name());
      no_cuts = keep_all_bits(f.type(), bitmap, from+f_width.offset, from+f_width.width) && no_cuts;
    }
    return no_cuts;
  }
  else if(const auto arr = type_try_dynamic_cast<array_typet>(tp)){
    bool no_cuts = true;
    if(!is_unbounded_array(tp))
    {
      const auto el_width = bv_width(arr->element_type());
      for(int i = from; i < to; i += el_width)
      {
        no_cuts = keep_all_bits(arr->element_type(), bitmap, i, i + el_width);
      }
    }
    return no_cuts;
  }
  return true;
}

bool boolbvt::is_abstractable_name(const std::basic_string<char> &name){
  if(name.find(CPROVER_PREFIX) == 0)
    return false;
  if(name.find("_cs_") != std::basic_string<char>::npos)
    return false;
  return true;
}

literalt boolbvt::convert_equality(const equal_exprt &expr)
{
  const bool equality_types_match = expr.lhs().type() == expr.rhs().type();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    equality_types_match,
    "types of expressions on each side of equality should match",
    irep_pretty_diagnosticst{expr.lhs()},
    irep_pretty_diagnosticst{expr.rhs()});

  // see if it is an unbounded array
  if(is_unbounded_array(expr.lhs().type()))
  {
    // flatten byte_update/byte_extract operators if needed

    if(has_byte_operator(expr))
    {
      return record_array_equality(
        to_equal_expr(lower_byte_operators(expr, ns)));
    }

    return record_array_equality(expr);
  }

  const bvt &lhs_bv = convert_bv(expr.lhs());

  optionalt<std::vector<bool>> abs_bitmap {};
  if(expr.get_long_long(ID_C_is_assignment) && !is_unbounded_array(expr.lhs().type()) && is_abstractable_name(as_string(to_ssa_expr(expr.lhs()).get_original_name())))
  {
    abs_bitmap = {std::vector<bool>(lhs_bv.size(), true)};
    if(keep_all_bits(expr.lhs().type(), *abs_bitmap, 0, abs_bitmap->size())){
      abs_bitmap = {};
    } else {
        const auto bitshuffle = endianness_map(expr.type());
        std::vector<bool> abs_bitmap_shuffled(lhs_bv.size(), true);
        for(size_t i=0; i<abs_bitmap->size(); i++)
          abs_bitmap_shuffled[bitshuffle.map_bit(i)] = (*abs_bitmap)[i];
        abs_bitmap = {abs_bitmap_shuffled};
    }
  }
  const bvt &rhs_bv = convert_bv(expr.rhs());

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs_bv.size() == rhs_bv.size(),
    "sizes of lhs and rhs bitvectors should match",
    irep_pretty_diagnosticst{expr.lhs()},
    "lhs size: " + std::to_string(lhs_bv.size()),
    irep_pretty_diagnosticst{expr.rhs()},
    "rhs size: " + std::to_string(rhs_bv.size()));

  if(lhs_bv.empty())
  {
    // An empty bit-vector comparison. It's not clear
    // what this is meant to say.
    return prop.new_variable();
  }

  return bv_utils.equal(lhs_bv, rhs_bv, abs_bitmap);
}

literalt boolbvt::convert_verilog_case_equality(
  const binary_relation_exprt &expr)
{
  // This is 4-valued comparison, i.e., z===z, x===x etc.
  // The result is always Boolean.

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    expr.lhs().type() == expr.rhs().type(),
    "lhs and rhs types should match in verilog_case_equality",
    irep_pretty_diagnosticst{expr.lhs()},
    irep_pretty_diagnosticst{expr.rhs()});

  const bvt &lhs_bv = convert_bv(expr.lhs());
  const bvt &rhs_bv = convert_bv(expr.rhs());

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs_bv.size() == rhs_bv.size(),
    "bitvector arguments to verilog_case_equality should have the same size",
    irep_pretty_diagnosticst{expr.lhs()},
    "lhs size: " + std::to_string(lhs_bv.size()),
    irep_pretty_diagnosticst{expr.rhs()},
    "rhs size: " + std::to_string(rhs_bv.size()));

  if(expr.id()==ID_verilog_case_inequality)
    return !bv_utils.equal(lhs_bv, rhs_bv);
  else
    return bv_utils.equal(lhs_bv, rhs_bv);
}
