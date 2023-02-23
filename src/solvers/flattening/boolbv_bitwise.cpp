/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_expr.h>

bvt boolbvt::convert_bitwise(const exprt &expr, const bwsize bitwidth)
{
  PRECONDITION(bitwidth & expr.get_int(ID_C_reduced_bitwidth));
  const std::size_t width = boolbv_width(expr.type());

  if(expr.id()==ID_bitnot)
  {
    const exprt &op = to_bitnot_expr(expr).op();
    PRECONDITION(bitwidth & op.get_int(ID_C_reduced_bitwidth));
    const bvt &op_bv = convert_bv(op, bitwidth, width);
    return bv_utils.inverted(op_bv);
  }
  else if(expr.id()==ID_bitand || expr.id()==ID_bitor ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitnand || expr.id()==ID_bitnor ||
          expr.id()==ID_bitxnor)
  {
    bvt bv;
    const auto reduced_width = (bitwidth == REDUCED) ? std::max((int)width, BWLEN) : width;
    bv.resize(reduced_width);

    forall_operands(it, expr)
    {
      PRECONDITION(bitwidth & it->get_int(ID_C_reduced_bitwidth));
      const bvt &op = convert_bv(*it, bitwidth, width);

      if(it==expr.operands().begin())
        bv=op;
      else
      {
        for(std::size_t i=0; i<reduced_width; i++)
        {
          if(expr.id()==ID_bitand)
            bv[i]=prop.land(bv[i], op[i]);
          else if(expr.id()==ID_bitor)
            bv[i]=prop.lor(bv[i], op[i]);
          else if(expr.id()==ID_bitxor)
            bv[i]=prop.lxor(bv[i], op[i]);
          else if(expr.id()==ID_bitnand)
            bv[i]=prop.lnand(bv[i], op[i]);
          else if(expr.id()==ID_bitnor)
            bv[i]=prop.lnor(bv[i], op[i]);
          else if(expr.id()==ID_bitxnor)
            bv[i]=prop.lequal(bv[i], op[i]);
          else
            UNIMPLEMENTED;
        }
      }
    }

    return bv;
  }

  UNIMPLEMENTED;
}
