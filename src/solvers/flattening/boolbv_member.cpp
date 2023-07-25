/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/c_types.h>
#include <util/namespace.h>

static bvt convert_member_union(
  const member_exprt &expr,
  const bvt &union_bv,
  const boolbvt &boolbv,
  const namespacet &ns)
{
  const exprt &union_op = expr.compound();
  const union_typet &union_op_type =
    ns.follow_tag(to_union_tag_type(union_op.type()));

  const irep_idt &component_name = expr.get_component_name();
  const union_typet::componentt &component =
    union_op_type.get_component(component_name);
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    component.is_not_nil(),
    "union type shall contain component accessed by member expression",
    expr.find_source_location(),
    id2string(component_name));

  const typet &subtype = component.type();
  const std::size_t sub_width = boolbv.boolbv_width(subtype);

  endianness_mapt map_u = boolbv.endianness_map(union_op_type);
  endianness_mapt map_component = boolbv.endianness_map(subtype);

  bvt result(sub_width, literalt{});
  for(std::size_t i = 0; i < sub_width; ++i)
    result[map_u.map_bit(i)] = union_bv[map_component.map_bit(i)];

  return result;
}

bvt boolbvt::convert_member(const member_exprt &expr)
{
  const bvt &compound_bv = convert_bv(expr.compound());

  const typet &compound_type = expr.compound().type();

  if(compound_type.id() == ID_struct_tag || compound_type.id() == ID_struct)
  {
    const struct_typet &struct_op_type =
      compound_type.id() == ID_struct_tag
        ? ns.follow_tag(to_struct_tag_type(compound_type))
        : to_struct_type(compound_type);

    const auto &member_bits =
      bv_width.get_member(struct_op_type, expr.get_component_name());

    INVARIANT(
      member_bits.offset + member_bits.width <= compound_bv.size(),
      "bitvector part corresponding to element shall be contained within the "
      "full aggregate bitvector");

    const auto should_abstract = !produce_nonabs(expr) && can_cast_type<integer_bitvector_typet>(expr.type()) && (int) to_integer_bitvector_type(expr.type()).get_width() > *abstraction_bits;
    if(should_abstract){
      const auto sign = to_integer_bitvector_type(expr.type()).smallest() < 0;
      const auto lit_cover = sign?compound_bv[member_bits.offset+*abstraction_bits-1]: const_literal(false);
      auto ans = bvt(compound_bv.begin() + member_bits.offset, compound_bv.begin() + member_bits.offset + *abstraction_bits);
      ans.insert(ans.end(), member_bits.width-*abstraction_bits, lit_cover);
      return ans;
    } else {
      return bvt(
        compound_bv.begin() + member_bits.offset,
        compound_bv.begin() + member_bits.offset + member_bits.width);
    }
  }
  else
  {
    PRECONDITION(
      compound_type.id() == ID_union_tag || compound_type.id() == ID_union);
    return convert_member_union(expr, compound_bv, *this, ns);
  }
}
