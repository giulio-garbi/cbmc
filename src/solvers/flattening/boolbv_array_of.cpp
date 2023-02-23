/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/std_types.h>

/// Flatten arrays constructed from a single element.
bvt boolbvt::convert_array_of(const array_of_exprt &expr, const bwsize bitwidth)
{
  DATA_INVARIANT(
    expr.type().id() == ID_array, "array_of expression shall have array type");

  PRECONDITION((bitwidth & expr.get_int(ID_C_reduced_bitwidth)) != 0);
  PRECONDITION(bitwidth == FULL);

  const array_typet &array_type = expr.type();

  if(is_unbounded_array(array_type))
    return conversion_failed(expr);

  std::size_t width=boolbv_width(array_type);
  if(width == 0)
    return bvt{};

  const exprt &array_size=array_type.size();

  const auto size = numeric_cast_v<mp_integer>(to_constant_expr(array_size));

  const bvt &tmp = convert_bv(expr.what(), (bwsize) expr.what().get_int(ID_C_reduced_bitwidth));

  INVARIANT(
    size * tmp.size() == width,
    "total array bit width shall equal the number of elements times the "
    "element bit with");

  bvt bv;
  bv.resize(width);

  auto b_it = tmp.begin();

  for(auto &b : bv)
  {
    b = *b_it;

    b_it++;

    if(b_it == tmp.end())
      b_it = tmp.begin();
  }

  return bv;
}
