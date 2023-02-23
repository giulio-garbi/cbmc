/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_expr.h>

bvt boolbvt::convert_bitreverse(const bitreverse_exprt &expr, const bwsize bitwidth)
{
  PRECONDITION(bitwidth & expr.get_int(ID_C_reduced_bitwidth));
  PRECONDITION(bitwidth & expr.op().get_int(ID_C_reduced_bitwidth));
  const std::size_t width = boolbv_width(expr.type());

  bvt bv = convert_bv(expr.op(), bitwidth, width);

  if(bitwidth == REDUCED) {
    //suppose that the lost bits are all 0s (since the bitreverse's argument is unsigned)
    int how_many_zeros = width - bv.size();
    bv.resize(std::max((int)(bv.size()-how_many_zeros), 0));
    std::reverse(bv.begin(), bv.end());
    bv.resize(BWLEN, const_literal(false));
  } else {
    std::reverse(bv.begin(), bv.end());
  }
  return bv;
}
