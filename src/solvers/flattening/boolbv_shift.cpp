/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <limits>

#include <util/arith_tools.h>

bvt boolbvt::convert_shift(const binary_exprt &expr)
{
  const irep_idt &type_id=expr.type().id();

  if(type_id!=ID_unsignedbv &&
     type_id!=ID_signedbv &&
     type_id!=ID_floatbv &&
     type_id!=ID_pointer &&
     type_id!=ID_bv &&
     type_id!=ID_verilog_signedbv &&
     type_id!=ID_verilog_unsignedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  const bvt &op = convert_bv(expr.op0(), width);

  bv_utilst::shiftt shift;

  if(expr.id()==ID_shl)
    shift=bv_utilst::shiftt::SHIFT_LEFT;
  else if(expr.id()==ID_ashr)
    shift=bv_utilst::shiftt::SHIFT_ARIGHT;
  else if(expr.id()==ID_lshr)
    shift=bv_utilst::shiftt::SHIFT_LRIGHT;
  else if(expr.id()==ID_rol)
    shift=bv_utilst::shiftt::ROTATE_LEFT;
  else if(expr.id()==ID_ror)
    shift=bv_utilst::shiftt::ROTATE_RIGHT;
  else
    UNREACHABLE;

  // we optimise for the special case where the shift distance
  // is a constant

  bv_utilst::representationt type_sign = type_id == ID_signedbv ? bv_utilst::representationt::SIGNED : bv_utilst::representationt::UNSIGNED;

  if(expr.op1().is_constant())
  {
    mp_integer i = numeric_cast_v<mp_integer>(to_constant_expr(expr.op1()));

    std::size_t distance;

    if(i<0 || i>std::numeric_limits<signed>::max())
      distance=0;
    else
      distance = numeric_cast_v<std::size_t>(i);

    if(type_id==ID_verilog_signedbv ||
       type_id==ID_verilog_unsignedbv)
      distance*=2;

    auto ans = bv_utils.shift(op, shift, distance);

    if(compute_bounds_failure(expr)){
      bounds_failure_literals[expr] = {bv_utils.bf_check(type_sign, *abstraction_bits, ans)};
    }
    if(!produce_nonabs(expr)){
      std::vector<int> abmap;
      bv_utils.abstraction_map(abmap, expr.type(), bv_width, *abstraction_bits, ns);
      ans = bv_utils.extract_abs_map(ans, abmap);
    }
    return ans;
  }
  else
  {
    const bvt &distance=convert_bv(expr.op1());
    auto ans = bv_utils.shift(op, shift, distance);

    if(compute_bounds_failure(expr)){
      bounds_failure_literals[expr] = {bv_utils.bf_check(type_sign, *abstraction_bits, ans)};
    }
    if(!produce_nonabs(expr)){
      std::vector<int> abmap;
      bv_utils.abstraction_map(abmap, expr.type(), bv_width, *abstraction_bits, ns);
      ans = bv_utils.extract_abs_map(ans, abmap);
    }
    return ans;
  }
}
