/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_types.h>

bvt boolbvt::convert_div(const div_exprt &expr)
{
  if(expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_signedbv &&
     expr.type().id()!=ID_fixedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  if(expr.op0().type().id()!=expr.type().id() ||
     expr.op1().type().id()!=expr.type().id())
    return conversion_failed(expr);

  bvt op0=convert_bv(expr.op0());
  bvt op1=convert_bv(expr.op1());

  if(op0.size()!=width ||
     op1.size()!=width)
    throw "convert_div: unexpected operand width";

  bvt res, rem;

  if(expr.type().id()==ID_fixedbv)
  {
    std::size_t fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();

    bvt zeros = bv_utils.zeros(fraction_bits);

    // add fraction_bits least-significant bits
    op0.insert(op0.begin(), zeros.begin(), zeros.end());
    op1=bv_utils.sign_extension(op1, op1.size()+fraction_bits);

    bv_utils.divider(op0, op1, res, rem, bv_utilst::representationt::SIGNED);

    // cut it down again
    res.resize(width);
  }
  else
  {
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                    bv_utilst::representationt::UNSIGNED;

    const size_t operation_max_width = produce_nonabs(expr)?width:std::min((int)width, *abstraction_bits);
    op0 = bv_utils.extract_lsb(op0, operation_max_width);
    op1 = bv_utils.extract_lsb(op1, operation_max_width);
    size_t div_bits = std::max(bv_utils.how_many_bits(rep, op0), bv_utils.how_many_bits(rep, op1));
    op0.resize(div_bits);
    op1.resize(div_bits);
    res.resize(div_bits);
    rem.resize(div_bits);

    bv_utils.divider(op0, op1, res, rem, rep);

    // overflow ::= (SIGNED && op0 == MAXINT_abs && op1 == -1)
    if(compute_bounds_failure(expr))
    {
      bvt of = bvt(1, const_literal(false));
      if(
        rep == bv_utilst::representationt::SIGNED &&
        (int) div_bits == *abstraction_bits)
      {
        op0[*abstraction_bits - 1].invert();
        of[0] = prop.land(prop.land(op0), prop.land(op1));
      }
      bounds_failure_literals[expr] = of;
    }
    res.resize(width, bv_utils.sign_bit(rep, res));
  }

  return res;
}
