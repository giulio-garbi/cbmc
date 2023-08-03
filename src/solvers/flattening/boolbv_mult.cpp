/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_types.h>

bvt boolbvt::convert_mult(const mult_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  bvt bv;
  bv.resize(width);

  const exprt::operandst &operands=expr.operands();
  DATA_INVARIANT(!operands.empty(), "multiplication must have operands");

  const exprt &op0=expr.op0();

  DATA_INVARIANT(
    op0.type() == expr.type(),
    "multiplication operands should have same type as expression");

  if(expr.type().id()==ID_fixedbv)
  {
    bv = convert_bv(op0, width);

    std::size_t fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();

    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      DATA_INVARIANT(
        it->type() == expr.type(),
        "multiplication operands should have same type as expression");

      // do a sign extension by fraction_bits bits
      bv=bv_utils.sign_extension(bv, bv.size()+fraction_bits);

      bvt op = convert_bv(*it, width);

      op=bv_utils.sign_extension(op, bv.size());

      bv=bv_utils.signed_multiplier(bv, op);

      // cut it down again
      bv.erase(bv.begin(), bv.begin()+fraction_bits);
    }

    return bv;
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv)
  {
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                    bv_utilst::representationt::UNSIGNED;
    bool should_abstract = !produce_nonabs(expr) && width > (size_t)*abstraction_bits;

    //const size_t operation_max_width = should_abstract?*abstraction_bits:width;
    bv = convert_bv(op0, width);
    if(should_abstract)
      bv = bv_utilst::extract_lsb(bv, *abstraction_bits);
    size_t mul_bits = bv_utils.how_many_bits(rep, bv);
    bvt of = bvt(1, const_literal(false));

    for(auto it=operands.begin()+1; it!=operands.end(); it++)
    {
      DATA_INVARIANT(
        it->type() == expr.type(),
        "multiplication operands should have same type as expression");

      bvt op = convert_bv(*it, width);//
      if(should_abstract)
        op = bv_utilst::extract_lsb(op, *abstraction_bits);
      size_t op_bits = bv_utils.how_many_bits(rep, op);
      mul_bits = mul_bits+op_bits;
      bv.resize(mul_bits, bv_utilst::sign_bit(rep, bv));
      op.resize(mul_bits, bv_utilst::sign_bit(rep, op));
      bv = bv_utils.multiplier(bv, op, rep);
      if(should_abstract && compute_bounds_failure(expr) && *abstraction_bits < (int) mul_bits) {
        of[0] = prop.lor(of[0], bv_utils.bf_check(rep, *abstraction_bits, bv));
      }
      if(should_abstract){
        bv.resize(*abstraction_bits, bv_utilst::sign_bit(rep, bv));
      } else {
        bv.resize(width, bv_utilst::sign_bit(rep, bv));
      }
      mul_bits = bv_utils.how_many_bits(rep, bv);
    }
    if(compute_bounds_failure(expr))
      bounds_failure_literals[expr] = of;
    if(bv.size() < width)
    {
      bv.resize(width, bv_utilst::sign_bit(rep, bv));
    }
    return bv;
  }

  return conversion_failed(expr);
}
