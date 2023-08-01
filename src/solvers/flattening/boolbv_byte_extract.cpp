/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

bvt map_bv(const endianness_mapt &map, const bvt &src)
{
  PRECONDITION(map.number_of_bits() == src.size());
  bvt result;
  result.reserve(src.size());

  for(std::size_t i=0; i<src.size(); i++)
  {
    const size_t mapped_index = map.map_bit(i);
    CHECK_RETURN(mapped_index < src.size());
    result.push_back(src[mapped_index]);
  }

  return result;
}

bvt boolbvt::convert_byte_extract(const byte_extract_exprt &expr)
{
  // array logic does not handle byte operators, thus lower when operating on
  // unbounded arrays
  if(is_unbounded_array(expr.op().type()))
  {
    return convert_bv(lower_byte_extract(expr, ns));
  }

  const std::size_t width = boolbv_width(expr.type());

  // special treatment for bit-fields and big-endian:
  // we need byte granularity
  #if 0
  if(expr.id()==ID_byte_extract_big_endian &&
     expr.type().id()==ID_c_bit_field &&
     (width%expr.get_bits_per_byte())!=0)
  {
    byte_extract_exprt tmp=expr;
    // round up
    to_c_bit_field_type(tmp.type()).set_width(
      width+expr.get_bits_per_byte()-width%expr.get_bits_per_byte());
    convert_byte_extract(tmp, bv);
    bv.resize(width); // chop down
    return;
  }
  #endif

  // see if the byte number is constant and within bounds, else work from the
  // root object
  const auto op_bytes_opt = pointer_offset_size(expr.op().type(), ns);
  auto index = numeric_cast<mp_integer>(expr.offset());
  auto prod_na = produce_nonabs(expr);

  if(
    (!index.has_value() || !op_bytes_opt.has_value() ||
     *index < 0 || *index >= *op_bytes_opt) &&
    (expr.op().id() == ID_member ||
     expr.op().id() == ID_index ||
     expr.op().id() == ID_byte_extract_big_endian ||
     expr.op().id() == ID_byte_extract_little_endian))
  {
    object_descriptor_exprt o;
    o.build(expr.op(), ns);
    CHECK_RETURN(o.offset().id() != ID_unknown);

    o.offset() =
      typecast_exprt::conditional_cast(o.offset(), expr.offset().type());

    byte_extract_exprt be(
      expr.id(),
      o.root_object(),
      plus_exprt(o.offset(), expr.offset()),
      expr.get_bits_per_byte(),
      expr.type());

    return convert_bv(be);
  }

  const exprt &op=expr.op();
  PRECONDITION(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian);
  const bool little_endian = expr.id() == ID_byte_extract_little_endian;

  // first do op0
  const endianness_mapt op_map = endianness_map(op.type(), little_endian);
  // TODO for more efficiency, convert op with a bitmap
  const bvt op_bv=map_bv(op_map, convert_bv(op));

  // do result
  endianness_mapt result_map = endianness_map(expr.type(), little_endian);
  bvt bv;
  bv.resize(width);

  // see if the byte number is constant
  if(index.has_value())
  {
    const mp_integer offset = *index * expr.get_bits_per_byte();

    for(std::size_t i=0; i<width; i++)
      // out of bounds?
      if(offset + i < 0 || offset + i >= op_bv.size())
        bv[i]=prop.new_variable();
      else
        bv[i] = op_bv[numeric_cast_v<std::size_t>(offset + i)];
  }
  else
  {
    std::size_t bytes = op_bv.size() / expr.get_bits_per_byte();

    if(prop.has_set_to())
    {
      // free variables
      std::vector<int> abmap;
      if(prod_na)
        bv = prop.new_variables(width);
      else{
        bv_utils.abstraction_map(abmap, expr.type(), bv_width, *abstraction_bits, ns);
        bv = bv_utils.new_var_abs_type(abmap);
      }


      // add implications

      // type of index operand
      const typet &constant_type = expr.offset().type();

      bvt equal_bv;
      equal_bv.resize(width);

      bvt offset_bv = convert_bv(expr.offset());
      auto offs_sign = to_integer_bitvector_type(expr.offset().type()).smallest() < 0 ? bv_utilst::representationt::SIGNED :bv_utilst::representationt::UNSIGNED;
      auto bits = bv_utils.how_many_bits(offs_sign,offset_bv) - (offs_sign == bv_utilst::representationt::SIGNED?1:0);
      for(std::size_t i=0; i<std::min(bytes, (size_t)1 << bits); i++)
      {
        std::size_t offset = i * expr.get_bits_per_byte();
        const auto offset_check = equal_exprt(expr.offset(), from_integer(i, constant_type));
        if(prod_na && produce_nonabs_map) //TODO or detect a pattern in offset
          (*produce_nonabs_map)[offset_check] = true;
        const literalt is_offset_ok = convert(offset_check);
        if(!is_offset_ok.is_false())
        {
          for(std::size_t j = 0; j < width; j++)
          {
            if(offset + j < op_bv.size() && (abmap.empty() || abmap[j] == (int)j))
              equal_bv[j] = prop.lequal(bv[j], op_bv[offset + j]);
            else
              equal_bv[j] = const_literal(true);
          }

          prop.l_set_to_true(prop.limplies(is_offset_ok, prop.land(equal_bv)));
        }
      }
    }
    else
    {
      // type of index operand
      const typet &constant_type = expr.offset().type();

      for(std::size_t i=0; i<bytes; i++)
      {
        literalt e =
          convert(equal_exprt(expr.offset(), from_integer(i, constant_type)));

        std::size_t offset = i * expr.get_bits_per_byte();

        for(std::size_t j=0; j<width; j++)
        {
          literalt l;

          if(offset+j<op_bv.size())
            l=op_bv[offset+j];
          else
            l=const_literal(false);

          if(i==0)
            bv[j]=l;
          else
            bv[j]=prop.lselect(e, l, bv[j]);
        }
      }
    }
  }

  // shuffle the result
  bv=map_bv(result_map, bv);

  if(compute_bounds_failure(expr)){
    auto rep = to_integer_bitvector_type(expr.type()).smallest() < 0 ? bv_utilst::representationt::SIGNED : bv_utilst::representationt::UNSIGNED;
    bounds_failure_literals[expr] = {bv_utils.bf_check(rep, *abstraction_bits, bv)};
  }
  if(!produce_nonabs(expr) && (int)bv.size() > *abstraction_bits && can_cast_type<integer_bitvector_typet>(expr.type())){
    auto rep = to_integer_bitvector_type(expr.type()).smallest() < 0 ? bv_utilst::representationt::SIGNED : bv_utilst::representationt::UNSIGNED;
    const auto lit_cover = rep == bv_utilst::representationt::UNSIGNED ? const_literal(false) : bv[*abstraction_bits-1];
    for(size_t idx = *abstraction_bits; idx < bv.size(); idx++)
      bv[idx] = lit_cover;
  }

  return bv;
}
