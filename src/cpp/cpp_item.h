/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_ITEM_H
#define CPROVER_CPP_CPP_ITEM_H

#include "cpp_declaration.h"
#include "cpp_linkage_spec.h"
#include "cpp_namespace_spec.h"
#include "cpp_using.h"
#include "cpp_static_assert.h"

class cpp_itemt:public irept
{
public:
  // declaration

  cpp_declarationt &make_declaration()
  {
    id(ID_cpp_declaration);
    return (cpp_declarationt &)*this;
  }

  cpp_declarationt &get_declaration()
  {
    PRECONDITION(is_declaration());
    return (cpp_declarationt &)*this;
  }

  const cpp_declarationt &get_declaration() const
  {
    PRECONDITION(is_declaration());
    return (const cpp_declarationt &)*this;
  }

  bool is_declaration() const
  {
    return id()==ID_cpp_declaration;
  }

  // linkage spec

  cpp_linkage_spect &make_linkage_spec()
  {
    id(ID_cpp_linkage_spec);
    return (cpp_linkage_spect &)*this;
  }

  cpp_linkage_spect &get_linkage_spec()
  {
    PRECONDITION(is_linkage_spec());
    return (cpp_linkage_spect &)*this;
  }

  const cpp_linkage_spect &get_linkage_spec() const
  {
    PRECONDITION(is_linkage_spec());
    return (const cpp_linkage_spect &)*this;
  }

  bool is_linkage_spec() const
  {
    return id()==ID_cpp_linkage_spec;
  }

  // namespace

  cpp_namespace_spect &make_namespace_spec()
  {
    id(ID_cpp_namespace_spec);
    return (cpp_namespace_spect &)*this;
  }

  cpp_namespace_spect &get_namespace_spec()
  {
    PRECONDITION(is_namespace_spec());
    return (cpp_namespace_spect &)*this;
  }

  const cpp_namespace_spect &get_namespace_spec() const
  {
    PRECONDITION(is_namespace_spec());
    return (const cpp_namespace_spect &)*this;
  }

  bool is_namespace_spec() const
  {
    return id()==ID_cpp_namespace_spec;
  }

  // using

  cpp_usingt &make_using()
  {
    id(ID_cpp_using);
    return (cpp_usingt &)*this;
  }

  cpp_usingt &get_using()
  {
    PRECONDITION(is_using());
    return (cpp_usingt &)*this;
  }

  const cpp_usingt &get_using() const
  {
    PRECONDITION(is_using());
    return (const cpp_usingt &)*this;
  }

  bool is_using() const
  {
    return id()==ID_cpp_using;
  }

  // static assertion

  cpp_static_assertt &make_static_assert()
  {
    id(ID_cpp_static_assert);
    return (cpp_static_assertt &)*this;
  }

  cpp_static_assertt &get_static_assert()
  {
    PRECONDITION(is_static_assert());
    return (cpp_static_assertt &)*this;
  }

  bool is_static_assert() const
  {
    return id()==ID_cpp_static_assert;
  }

  const source_locationt &source_location() const
  {
    return static_cast<const source_locationt &>(
      find(ID_C_source_location));
  }
};

#endif // CPROVER_CPP_CPP_ITEM_H
