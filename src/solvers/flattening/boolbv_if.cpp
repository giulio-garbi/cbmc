/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_if(const if_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return bvt(); // An empty bit-vector if.

  literalt cond=convert(expr.cond());

  bvt true_case_bv = convert_bv(expr.true_case(), width);
  bvt false_case_bv = convert_bv(expr.false_case(), width);

  /*if(!is_unbounded_array(expr.type()) && (is_abstract_op(expr.true_case()) || is_abstract_op(expr.false_case()))){
    std::vector<bool> abs_bitmap(true_case_bv.size(), true);
    if(!keep_all_bits(expr.type(), abs_bitmap, 0, abs_bitmap.size())){
      const auto bitshuffle = endianness_map(expr.type());
      std::vector<bool> abs_bitmap_shuffled(true_case_bv.size(), true);
      for(size_t i=0; i<abs_bitmap.size(); i++)
        abs_bitmap_shuffled[bitshuffle.map_bit(i)] = abs_bitmap[i];
      return bv_utils.select_with_mask(cond, true_case_bv, false_case_bv, abs_bitmap_shuffled);
    }
  }*/
  if(!is_unbounded_array(expr.type()) && !produce_nonabs(expr) && (int)width > *abstraction_bits){
    true_case_bv = bv_utils.extract_lsb(true_case_bv, *abstraction_bits);
    false_case_bv = bv_utils.extract_lsb(false_case_bv, *abstraction_bits);
  }
  auto ans = bv_utils.select(cond, true_case_bv, false_case_bv);
  auto rep = expr.type().id() == ID_signedbv?bv_utilst::representationt::SIGNED: bv_utilst::representationt::UNSIGNED;
  ans.resize(width, bv_utils.sign_bit(rep, ans));
  return ans;
}
