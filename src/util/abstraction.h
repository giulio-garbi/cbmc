//
// Created by giulio on 25/05/23.
//

#ifndef CBMC_ABSTRACTION_H
#define CBMC_ABSTRACTION_H

#include <util/ssa_expr.h>

#include "bitvector_types.h"

#include "goto-symex/symex_target_equation.h"

unsignedbv_typet get_abs_type(typet &t, namespacet &ns);

class is_abstractt: public unary_exprt{
public:
  is_abstractt(ssa_exprt &expr) : unary_exprt(ID_is_abstract, expr, bool_typet{}){}
};


inline bool is_is_abstract(const exprt &expr)
{
  return expr.id() == ID_is_abstract;
}

template <>
inline bool can_cast_expr<is_abstractt>(const exprt &base)
{
  return is_is_abstract(base);
}

/// Cast a generic exprt to an \ref is_abstractt.
/// \param expr: Source expression
/// \return Object of type \ref is_abstractt
inline const is_abstractt &to_is_abstract(const exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_is_abstract(expr), "expr needs to be a is_abstractt", expr.pretty());
  return static_cast<const is_abstractt &>(expr);
}

/// \copydoc to_is_abstract(const exprt &)
inline is_abstractt &to_is_abstract(exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_is_abstract(expr), "expr needs to be a is_abstractt", expr.pretty());
  return static_cast<is_abstractt &>(expr);
}

class bounds_failuret: public unary_exprt{
public:
  bounds_failuret(const exprt &expr, size_t width) : unary_exprt(ID_bounds_failure, expr, unsignedbv_typet(1)){
    set(ID_width, width);
  }
};


inline bool is_bounds_failure(const exprt &expr)
{
  return expr.id() == ID_bounds_failure;
}

template <>
inline bool can_cast_expr<bounds_failuret>(const exprt &base)
{
  return is_bounds_failure(base);
}

/// Cast a generic exprt to an \ref bounds_failuret.
/// \param expr: Source expression
/// \return Object of type \ref bounds_failuret
inline const bounds_failuret &to_bounds_failure(const exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_bounds_failure(expr), "expr needs to be a bounds_failuret", expr.pretty());
  return static_cast<const bounds_failuret &>(expr);
}

/// \copydoc to_bounds_failure(const exprt &)
inline bounds_failuret &to_bounds_failure(exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_bounds_failure(expr), "expr needs to be a bounds_failuret", expr.pretty());
  return static_cast<bounds_failuret &>(expr);
}

//const exprt is_expr_abstract(exprt&, size_t width);
bool is_abstractable_name(const std::string);
bool is_abstractable_type(const typet&, size_t, symex_target_equationt&);
void apply_approx(symex_target_equationt &targetEquation, size_t width, namespacet &ns);
void annotate_ssa_exprs_tree(symex_target_equationt& targetEquation);



#endif //CBMC_ABSTRACTION_H
