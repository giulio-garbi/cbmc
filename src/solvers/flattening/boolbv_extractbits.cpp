/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>

#include "bitvector_types.h"
#include "boolbv.h"

bvt boolbvt::convert_extractbits(const extractbits_exprt &expr)
{
  const std::size_t bv_width = boolbv_width(expr.type());

  auto const &src_bv = convert_bv(expr.src());

  auto const maybe_upper_as_int = numeric_cast<mp_integer>(expr.upper());
  auto const maybe_lower_as_int = numeric_cast<mp_integer>(expr.lower());

  // We only do constants for now.
  // Should implement a shift here.
  if(!maybe_upper_as_int.has_value() || !maybe_lower_as_int.has_value())
    return conversion_failed(expr);

  auto upper_as_int = maybe_upper_as_int.value();
  auto lower_as_int = maybe_lower_as_int.value();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    upper_as_int >= 0 && upper_as_int < src_bv.size(),
    "upper end of extracted bits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lower_as_int >= 0 && lower_as_int < src_bv.size(),
    "lower end of extracted bits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  DATA_INVARIANT(
    lower_as_int <= upper_as_int,
    "upper bound must be greater or equal to lower bound");

  // now lower_as_int <= upper_as_int

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    (upper_as_int - lower_as_int + 1) == bv_width,
    "the difference between upper and lower end of the range must have the "
    "same width as the resulting bitvector type",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  const std::size_t offset = numeric_cast_v<std::size_t>(lower_as_int);

  bvt result_bv(src_bv.begin() + offset, src_bv.begin() + offset + bv_width);
  if(compute_bounds_failure(expr)){
    auto rep = to_integer_bitvector_type(expr.type()).smallest() < 0 ? bv_utilst::representationt::SIGNED : bv_utilst::representationt::UNSIGNED;
    bounds_failure_literals[expr] = {bv_utils.bf_check(rep, *abstraction_bits, result_bv)};
  }
  if(!produce_nonabs(expr) && (int)result_bv.size() > *abstraction_bits && can_cast_type<integer_bitvector_typet>(expr.type())){
    auto rep = to_integer_bitvector_type(expr.type()).smallest() < 0 ? bv_utilst::representationt::SIGNED : bv_utilst::representationt::UNSIGNED;
    const auto lit_cover = rep == bv_utilst::representationt::UNSIGNED ? const_literal(false) : result_bv[*abstraction_bits-1];
    for(size_t idx = *abstraction_bits; idx < result_bv.size(); idx++)
      result_bv[idx] = lit_cover;
  }

  return result_bv;
}
