/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_mod(const mod_exprt &expr)
{
  #if 0
  // TODO
  if(expr.type().id()==ID_floatbv)
  {
  }
  #endif

  if(expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_signedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  DATA_INVARIANT(
    expr.dividend().type().id() == expr.type().id(),
    "type of the dividend of a modulo operation shall equal the "
    "expression type");

  DATA_INVARIANT(
    expr.divisor().type().id() == expr.type().id(),
    "type of the divisor of a modulo operation shall equal the "
    "expression type");

  bv_utilst::representationt rep=
    expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                  bv_utilst::representationt::UNSIGNED;

  bvt dividend_bv = convert_bv(expr.dividend(), width);
  bvt divisor_bv = convert_bv(expr.divisor(), width);

  auto nbits = std::max(bv_utils.how_many_bits(rep, dividend_bv), bv_utils.how_many_bits(rep, divisor_bv));
  if(rep == bv_utilst::representationt::SIGNED)
  {
    bool might_dividend_maxint = true, might_divisor_minus1 = true;
    for(unsigned long i = 0; i < nbits; i++)
    {
      if(divisor_bv[i].is_false())
        might_divisor_minus1 = false;
      if(i == nbits - 2)
      {
        if(dividend_bv[i].is_false())
          might_dividend_maxint = false;
      } else {
        if(dividend_bv[i].is_true())
          might_dividend_maxint = false;
      }
    }
    if(might_dividend_maxint && might_divisor_minus1)
      nbits = nbits+1;
  }
  nbits = std::min(nbits, width);
  if(!produce_nonabs(expr))
    nbits = std::min(nbits, (size_t)*abstraction_bits);
  dividend_bv.resize(nbits);
  divisor_bv.resize(nbits);
  bvt res, rem;

  bv_utils.divider(dividend_bv, divisor_bv, res, rem, rep);

  if(nbits != width){
    res.resize(width, bv_utilst::sign_bit(rep, res));
    rem.resize(width, bv_utilst::sign_bit(rep, rem));
  }

  return rem;
}
