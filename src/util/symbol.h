/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SYMBOL_H
#define CPROVER_UTIL_SYMBOL_H

/// \file util/symbol.h
/// \brief Symbol table entry
/// \author Daniel Kroening <kroening@kroening.com>
/// \date   Sun Jul 31 21:54:44 BST 2011

#include <iosfwd>

#include "expr.h"
#include "invariant.h"

/// \brief Symbol table entry.
/// \ingroup gr_symbol_table
/// This is a symbol in the symbol table, stored in an
/// object of type symbol_tablet.
class symbolt
{
public:
  /// Type of symbol
  typet type;

  /// Initial value of symbol
  exprt value;

  /// Source code location of definition of symbol
  source_locationt location;

  /// The unique identifier
  irep_idt name;

  /// Name of module the symbol belongs to
  irep_idt module;

  /// Base (non-scoped) name
  irep_idt base_name;

  /// Language mode
  irep_idt mode;

  /// Language-specific display name
  irep_idt pretty_name;

  /// Return language specific display name if present.
  const irep_idt &display_name() const
  {
    return pretty_name.empty()?name:pretty_name;
  }

  // global use
  bool is_type = false;
  bool is_macro = false;
  bool is_exported = false;
  bool is_input = false;
  bool is_output = false;
  bool is_state_var = false;
  bool is_property = false;

  // ANSI-C
  bool is_static_lifetime = false;
  bool is_thread_local = false;
  bool is_lvalue = false;
  bool is_file_local = false;
  bool is_extern = false;
  bool is_volatile = false;
  bool is_parameter = false;
  bool is_auxiliary = false;
  bool is_weak = false;

  symbolt()
    : type(static_cast<const typet &>(get_nil_irep())),
      value(static_cast<const exprt &>(get_nil_irep())),
      location(source_locationt::nil())
  {
  }

  symbolt(const irep_idt &_name, typet _type, const irep_idt &_mode)
    : type(std::move(_type)),
      value(static_cast<const exprt &>(get_nil_irep())),
      location(source_locationt::nil()),
      name(_name),
      mode(_mode)
  {
  }

  void swap(symbolt &b);
  void show(std::ostream &out) const;

  class symbol_exprt symbol_expr() const;

  bool is_shared() const
  {
    return !is_thread_local;
  }

  bool is_function() const
  {
    return !is_type && !is_macro && type.id()==ID_code;
  }

  /// Returns true iff the the symbol's value has been compiled to a goto
  /// program.
  bool is_compiled() const
  {
    return type.id() == ID_code && value == exprt(ID_compiled);
  }

  /// Set the symbol's value to "compiled"; to be used once the code-typed value
  /// has been converted to a goto program.
  void set_compiled()
  {
    PRECONDITION(type.id() == ID_code);
    value = exprt(ID_compiled);
  }

  /// Check that a symbol is well formed.
  bool is_well_formed() const;

  bool operator==(const symbolt &other) const;
  bool operator!=(const symbolt &other) const;
};

std::ostream &operator<<(std::ostream &out, const symbolt &symbol);

/// \brief Symbol table entry describing a data type
/// \ingroup gr_symbol_table
/// This is a symbol generated as part of type checking.
class type_symbolt:public symbolt
{
public:
  type_symbolt(const irep_idt &_name, typet _type, const irep_idt &_mode)
    : symbolt(_name, _type, _mode)
  {
    is_type = true;
  }
};

/// \brief Internally generated symbol table entry
/// \ingroup gr_symbol_table
/// This is a symbol generated as part of translation to or
/// modification of the intermediate representation.
class auxiliary_symbolt:public symbolt
{
public:
  auxiliary_symbolt()
  {
    is_lvalue=true;
    is_state_var=true;
    is_thread_local=true;
    is_file_local=true;
    is_auxiliary=true;
  }

  auxiliary_symbolt(const irep_idt &name, typet type, const irep_idt &mode)
    : symbolt(name, type, mode)
  {
    is_lvalue = true;
    is_state_var = true;
    is_thread_local = true;
    is_file_local = true;
    is_auxiliary = true;
  }
};

/// \brief Symbol table entry of function parameter
/// \ingroup gr_symbol_table
/// This is a symbol generated as part of type checking.
class parameter_symbolt:public symbolt
{
public:
  parameter_symbolt()
  {
    is_lvalue=true;
    is_state_var=true;
    is_thread_local=true;
    is_file_local=true;
    is_parameter=true;
  }
};

#endif // CPROVER_UTIL_SYMBOL_H
