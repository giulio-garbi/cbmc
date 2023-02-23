/*******************************************************************\

Module: Bit-blasting of bswap

Author: Michael Tautschnig

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_expr.h>

bvt boolbvt::convert_bswap(const bswap_exprt &expr, const bwsize bitwidth)
{
  PRECONDITION(bitwidth & expr.get_int(ID_C_reduced_bitwidth));
  PRECONDITION(bitwidth & expr.op().get_int(ID_C_reduced_bitwidth));
  const std::size_t width = boolbv_width(expr.type());

  // width must be multiple of bytes
  const std::size_t byte_bits = expr.get_bits_per_byte();
  if(width % byte_bits != 0)
    return conversion_failed(expr);

  bvt result = convert_bv(expr.op(), bitwidth, width);
  int numzeros = width - result.size();
  if(bitwidth == REDUCED && numzeros>0)
    result.insert(result.begin(), numzeros, const_literal(false));

  std::size_t dest_base = width;

  for(std::size_t src = 0; src < width; ++src)
  {
    std::size_t bit_offset = src % byte_bits;
    if(bit_offset == 0)
      dest_base -= byte_bits;

    if(src >= dest_base)
      break;

    result[src].swap(result[dest_base + bit_offset]);
  }

  if(bitwidth == REDUCED && numzeros>0)
    result.erase(result.begin(), result.begin()+numzeros);

  return result;
}
