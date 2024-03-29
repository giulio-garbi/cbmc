/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_SCOPES_H
#define CPROVER_CPP_CPP_SCOPES_H

#include <set>

#include "cpp_scope.h"

class symbolt;

class cpp_scopest
{
public:
  cpp_scopest()
  {
    current_scope_ptr=&root_scope;
  }

  typedef std::set<cpp_scopet *> scope_sett;
  typedef std::set<cpp_idt *> id_sett;

  cpp_scopet &current_scope()
  {
    return *current_scope_ptr;
  }

  cpp_scopet &new_scope(
    const irep_idt &new_scope_name,
    cpp_idt::id_classt id_class)
  {
    PRECONDITION(!new_scope_name.empty());
    cpp_scopet &n=current_scope_ptr->new_scope(new_scope_name);
    n.id_class=id_class;
    id_map[n.identifier]=&n;
    current_scope_ptr=&n;
    return n;
  }

  cpp_scopet &new_namespace(const irep_idt &new_scope_name)
  {
    return new_scope(new_scope_name, cpp_idt::id_classt::NAMESPACE);
  }

  cpp_scopet &new_block_scope();

  cpp_idt &put_into_scope(
    const symbolt &symbol,
    cpp_scopet &scope,
    bool is_friend = false);

  cpp_idt &put_into_scope(const symbolt &symbol, bool is_friend = false)
  {
    return put_into_scope(symbol, current_scope(), is_friend);
  }

  // mapping from function/class/scope names to their cpp_idt
  typedef std::unordered_map<irep_idt, cpp_idt *> id_mapt;
  id_mapt id_map;

  cpp_scopet *current_scope_ptr;

  cpp_idt &get_id(const irep_idt &identifier)
  {
    id_mapt::const_iterator it=id_map.find(identifier);
    if(it==id_map.end())
      throw "id '" + id2string(identifier) + "' not found";
    return *(it->second);
  }

  cpp_scopet &get_scope(const irep_idt &identifier)
  {
    cpp_idt &n=get_id(identifier);
    CHECK_RETURN(n.is_scope);
    return (cpp_scopet &)n;
  }

  cpp_scopet &set_scope(const irep_idt &identifier)
  {
    current_scope_ptr=&get_scope(identifier);
    return current_scope();
  }

  cpp_scopet &get_root_scope()
  {
    return root_scope;
  }

  void go_to_root_scope()
  {
    current_scope_ptr=&root_scope;
  }

  void go_to(cpp_idt &id)
  {
    PRECONDITION(id.is_scope);
    current_scope_ptr=static_cast<cpp_scopet*>(&id);
  }

  // move up to next global scope
  void go_to_global_scope()
  {
    current_scope_ptr=&get_global_scope();
  }

  cpp_scopet &get_global_scope()
  {
    return current_scope().get_global_scope();
  }

  void print_current(std::ostream &out) const;

protected:
  // the root scope
  cpp_root_scopet root_scope;
};

class cpp_save_scopet
{
public:
  explicit cpp_save_scopet(cpp_scopest &_cpp_scopes):
    cpp_scopes(_cpp_scopes),
    saved_scope(_cpp_scopes.current_scope_ptr)
  {
  }

  ~cpp_save_scopet()
  {
    restore();
  }

  void restore()
  {
    cpp_scopes.current_scope_ptr=saved_scope;
  }

protected:
  cpp_scopest &cpp_scopes;
  cpp_scopet *saved_scope;
};

#endif // CPROVER_CPP_CPP_SCOPES_H
