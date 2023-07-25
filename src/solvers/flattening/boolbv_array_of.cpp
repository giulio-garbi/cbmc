/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/std_types.h>

#include "bitvector_types.h"
#include "boolbv.h"

/// Flatten arrays constructed from a single element.
bvt boolbvt::convert_array_of(const array_of_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_array, "array_of expression shall have array type");

  const array_typet &array_type = expr.type();

  if(is_unbounded_array(array_type))
    return conversion_failed(expr);

  std::size_t width=boolbv_width(array_type);
  if(width == 0)
    return bvt{};

  const exprt &array_size=array_type.size();

  const auto size = numeric_cast_v<mp_integer>(to_constant_expr(array_size));

  bvt tmp = convert_bv(expr.what());
  const auto should_abstract = !produce_nonabs(expr) && can_cast_type<integer_bitvector_typet>(expr.what().type()) && (int)to_integer_bitvector_type(expr.what().type()).get_width() > *abstraction_bits;
  if(should_abstract){
    const auto sign = to_integer_bitvector_type(expr.what().type()).smallest() < 0;
    const auto lit_cover = sign?tmp[*abstraction_bits-1]: const_literal(false);
    for(size_t i = *abstraction_bits; i < tmp.size(); i++)
      tmp[i] = lit_cover;
  }

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
