/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/invariant.h>

#include "bitvector_types.h"
#include "boolbv.h"

/// Flatten array. Loop over each element and convert them in turn, limiting
/// each result's width to initial array bit size divided by number of elements.
/// Return an empty vector if the width is zero or the array has no elements.
bvt boolbvt::convert_array(const exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());
  const exprt::operandst &operands = expr.operands();

  if(operands.empty() && width == 0)
    return bvt();

  if(expr.type().id()==ID_array)
  {
    DATA_INVARIANT(
      expr.has_operands(),
      "the bit width being nonzero implies that the array has a nonzero size "
      "in which case the array shall have operands");
    const std::size_t op_width = width / operands.size();

    bvt bv;
    bv.reserve(width);

    const auto elem_type = to_array_type(expr.type()).element_type();
    const auto should_abstract = !produce_nonabs(expr) && can_cast_type<integer_bitvector_typet>(elem_type) && (int) to_integer_bitvector_type(elem_type).get_width() > *abstraction_bits;
    const auto sign = should_abstract && to_integer_bitvector_type(elem_type).smallest() < 0;

    for(const auto &op : operands)
    {
      const bvt &tmp = convert_bv(op, op_width);

      if(should_abstract)
      {
        bv.insert(bv.end(), tmp.begin(), tmp.begin()+*abstraction_bits);
        auto lit_cover = sign?tmp[*abstraction_bits-1]: const_literal(false);
        bv.insert(bv.end(), op_width-*abstraction_bits, lit_cover);
      } else {
        bv.insert(bv.end(), tmp.begin(), tmp.end());
      }
    }

    return bv;
  }

  return conversion_failed(expr);
}
