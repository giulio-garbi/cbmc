/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/invariant.h>

#include "boolbv.h"
#include "ssa_expr.h"

bool boolbvt::is_abstract_op(const exprt& expr){
  if(const auto ssa = expr_try_dynamic_cast<ssa_exprt>(expr)){
    return is_abstractable_name(as_string(ssa->get_original_name()));
  }
  else if (const auto bu = expr_try_dynamic_cast<byte_update_exprt>(expr)){
    return is_abstract_op(bu->op());
  }
  else if (const auto ife = expr_try_dynamic_cast<if_exprt>(expr)){
    return is_abstract_op(ife->true_case()) || is_abstract_op(ife->false_case());
  }
  else if (const auto cast = expr_try_dynamic_cast<typecast_exprt>(expr)){
    return is_abstract_op(cast->op());
  }
  else if (const auto arr = expr_try_dynamic_cast<array_exprt>(expr)){
    for(const auto &item : arr->operands()){
      if(is_abstract_op(item))
        return true;
    }
  }
  else if (const auto str = expr_try_dynamic_cast<struct_exprt>(expr)){
    for(const auto &item : str->operands()){
      if(is_abstract_op(item))
        return true;
    }
  }
  return false;
}

bvt boolbvt::convert_byte_update(const byte_update_exprt &expr)
{
  // if we update (from) an unbounded array, lower the expression as the array
  // logic does not handle byte operators
  if(
    is_unbounded_array(expr.op().type()) ||
    is_unbounded_array(expr.value().type()))
  {
    return convert_bv(lower_byte_update(expr, ns));
  }

  const exprt &op = expr.op();
  const exprt &offset_expr=expr.offset();
  const exprt &value=expr.value();

  PRECONDITION(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian);
  const bool little_endian = expr.id() == ID_byte_update_little_endian;

  bvt bv=convert_bv(op);

  const bvt &value_bv=convert_bv(value);
  std::size_t update_width=value_bv.size();
  std::size_t byte_width = expr.get_bits_per_byte();

  optionalt<std::vector<bool>> abs_bitmap {};
  if(!is_unbounded_array(op.type()) && is_abstract_op(op)){
    abs_bitmap = {std::vector<bool>(bv.size(), true)};
    if(keep_all_bits(op.type(), *abs_bitmap, 0, abs_bitmap->size()))
      abs_bitmap = {};
  }

  if(update_width>bv.size())
    update_width=bv.size();

  // see if the byte number is constant

  const auto index = numeric_cast<mp_integer>(offset_expr);
  if(index.has_value())
  {
    // yes!
    const mp_integer offset = *index * byte_width;

    if(offset+update_width>mp_integer(bv.size()) || offset<0)
    {
      // out of bounds
    }
    else
    {
      endianness_mapt map_op = endianness_map(op.type(), little_endian);
      endianness_mapt map_value = endianness_map(value.type(), little_endian);

      const std::size_t offset_i = numeric_cast_v<std::size_t>(offset);

      for(std::size_t i = 0; i < update_width; i++)
      {
        size_t index_op = map_op.map_bit(offset_i + i);
        size_t index_value = map_value.map_bit(i);

        INVARIANT(
          index_op < bv.size(), "bit vector index shall be within bounds");
        INVARIANT(
          index_value < value_bv.size(),
          "bit vector index shall be within bounds");

        bv[index_op] = (abs_bitmap && !(*abs_bitmap)[offset_i + i]) ? const_literal(false) : value_bv[index_value];
      }
    }

    return bv;
  }

  // byte_update with variable index
  for(std::size_t offset=0; offset<bv.size(); offset+=byte_width)
  {
    // index condition
    equal_exprt equality(
      offset_expr, from_integer(offset / byte_width, offset_expr.type()));
    literalt equal=convert(equality);

    endianness_mapt map_op = endianness_map(op.type(), little_endian);
    endianness_mapt map_value = endianness_map(value.type(), little_endian);

    for(std::size_t bit=0; bit<update_width; bit++)
      if(offset+bit<bv.size())
      {
        std::size_t bv_o=map_op.map_bit(offset+bit);
        std::size_t value_bv_o=map_value.map_bit(bit);

        bv[bv_o]=(abs_bitmap && !(*abs_bitmap)[offset+bit]) ? const_literal(false) : prop.lselect(equal, value_bv[value_bv_o], bv[bv_o]);
        ;
      }
  }

  return bv;
}
