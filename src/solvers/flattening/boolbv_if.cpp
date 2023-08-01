/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bitvector_types.h"
#include "boolbv.h"

bvt boolbvt::convert_if(const if_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return bvt(); // An empty bit-vector if.

  literalt cond=convert(expr.cond());

  bvt true_case_bv = convert_bv(expr.true_case(), width);
  bvt false_case_bv = convert_bv(expr.false_case(), width);

  if(!is_unbounded_array(expr.type()) && !produce_nonabs(expr) && (produce_nonabs(expr.true_case()) || produce_nonabs(expr.false_case()))){
    std::vector<int> abmap;
    bv_utilst::abstraction_map(abmap, expr.type(), bv_width, *abstraction_bits, ns);
    if(produce_nonabs(expr.true_case()))
      true_case_bv = bv_utilst::extract_abs_map(true_case_bv, abmap);
    if(produce_nonabs(expr.false_case()))
      false_case_bv = bv_utilst::extract_abs_map(false_case_bv, abmap);
  }
  auto ans = bv_utils.select(cond, true_case_bv, false_case_bv);
  /*auto rep = expr.type().id() == ID_signedbv?bv_utilst::representationt::SIGNED: bv_utilst::representationt::UNSIGNED;
  if(!is_unbounded_array(expr.type()) && !produce_nonabs(expr) && can_cast_type<integer_bitvector_typet>(expr.type()) && (int)width > *abstraction_bits)
  {
    ans.resize(width, bv_utilst::sign_bit(rep, ans));
  }*/
  return ans;
}
