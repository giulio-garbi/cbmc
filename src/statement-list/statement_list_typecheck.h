/*******************************************************************\

Module: Statement List Language Type Checking

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Type Checking

#ifndef CPROVER_STATEMENT_LIST_STATEMENT_LIST_TYPECHECK_H
#define CPROVER_STATEMENT_LIST_STATEMENT_LIST_TYPECHECK_H

#include <util/std_code_base.h>
#include <util/typecheck.h>

#include "statement_list_parse_tree.h"

class code_frontend_assignt;
class code_labelt;
class symbol_table_baset;
class symbolt;

/// Create a new statement_list_typecheckt object and perform a type check to
/// fill the symbol table.
/// \param parse_tree: Parse tree generated by parsing a Statement List file.
/// \param [out] symbol_table: Object that shall be filled by this function.
///   If the symbol table is not empty when calling this function, its contents
///   are merged with the new entries.
/// \param module: Name of the file that has been parsed.
/// \param message_handler: Used to provide debug information and error
///   messages.
/// \return False if no errors occurred, true otherwise.
bool statement_list_typecheck(
  const statement_list_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

/// Class for encapsulating the current state of the type check.
class statement_list_typecheckt : public typecheckt
{
public:
  /// Creates a new instance of statement_list_typecheckt.
  /// \param parse_tree: Parse tree generated by parsing a Statement List file.
  /// \param [out] symbol_table: Object that shall be filled by this function.
  ///   If the symbol table is not empty when calling this function, its
  ///   contents are merged with the new entries.
  /// \param module: Name of the file that has been parsed.
  /// \param message_handler: Used to provide debug information and error
  ///   messages.
  statement_list_typecheckt(
    const statement_list_parse_treet &parse_tree,
    symbol_table_baset &symbol_table,
    const std::string &module,
    message_handlert &message_handler);

  /// Performs the actual typecheck by using the parse tree with which the
  /// object was initialized and modifies the referenced symbol table.
  void typecheck() override;

private:
  /// Parse tree which is used to fill the symbol table.
  const statement_list_parse_treet &parse_tree;

  /// Reference to the symbol table that should be filled during the typecheck.
  symbol_table_baset &symbol_table;

  /// Name of the module this typecheck belongs to.
  const irep_idt module;

  // Internal state of the PLC program
  // TODO: Implement complete status word representation.
  // See the Siemens documentation for further details.

  /// Representation of the accumulator of a TIA element.
  std::vector<exprt> accumulator;

  /// Result of Logic Operation (Part of the TIA status word). Holds the
  /// current boolean expression of the active network and is read and modified
  /// by boolean instructions.
  exprt rlo_bit = true_exprt();

  /// First Check (Part of the TIA status word). Gets set every time a boolean
  /// instruction is encountered and is set to false once the boolean
  /// expression as a whole is terminated (either by an assignment or other
  /// instructions).
  bool fc_bit = false;

  /// Or (Part of the TIA status word). Helps to track all And instructions
  /// that follow an operand-less Or instruction (The so called 'And before
  /// Or').
  bool or_bit = false;

  /// Every time branching occurs inside of a boolean expression string in STL,
  /// the current value of the RLO and OR bits are saved and put on a separate
  /// stack. After returning from the branch, these values are popped and
  /// replace the current status word bits.
  struct nesting_stack_entryt
  {
    /// The rlo's value when the entry was generated.
    exprt rlo_bit;

    /// The OR bit's value when the entry was generated.
    bool or_bit = false;

    /// OP code of the instruction that generated the stack entry.
    codet function_code;

    nesting_stack_entryt(exprt rlo_bit, bool or_bit, codet function_code);
  };
  using nesting_stackt = std::vector<nesting_stack_entryt>;

  /// Representation of the nesting stack. Values are pushed once branching
  /// occurs and popped upon returning.
  nesting_stackt nesting_stack;

  /// Holds information about the instruction and the nesting depth to which a
  /// label points.
  struct stl_label_locationt
  {
    /// The size of the nesting stack at the label location, used for checking
    /// scope violations.
    const size_t nesting_depth;

    /// States if jumps to this location are permitted or if the location is
    /// invalid.
    const bool jumps_permitted;

    /// States if jump instructions to this location need to set the /FC bit to
    /// false.
    const bool fc_false_required;

    /// Constructs a new location with the specified properties.
    /// \param nesting_depth: Scope of the label.
    /// \param jumps_permitted: States whether jumps to the label are possible
    ///   in general.
    /// \param fc_false_required: States whether a jump instruction to this
    ///   label needs to set the /FC bit.
    stl_label_locationt(
      size_t nesting_depth,
      bool jumps_permitted,
      bool fc_false_required);
  };
  using stl_labelst = std::unordered_map<irep_idt, stl_label_locationt>;

  /// Data structure that contains data about the labels of the current module.
  stl_labelst stl_labels;

  /// Holds information about the properties of a jump instruction.
  struct stl_jump_locationt
  {
    // TODO: Add source location to the structure.
    // Requires the source location to be added to the parser in general.

    /// The size of the nesting stack at the label location, used for checking
    /// scope violations.
    const size_t nesting_depth;

    /// States if the jump instruction sets the /FC bit to false.
    const bool sets_fc_false;

    /// Constructs a new location with the specified properties.
    /// \param nesting_depth: Scope of the jump instruction.
    /// \param sets_fc_false: States whether the jump instruction modifies the
    ///   /FC bit.
    stl_jump_locationt(size_t nesting_depth, bool sets_fc_false);
  };
  using label_referencest =
    std::unordered_map<irep_idt, std::vector<stl_jump_locationt>>;

  /// Holds associations between labels and jumps that are referencing it.
  /// This list should be empty after a successful typecheck. A new entry is
  /// added only if a jump is encountered that references an unknown label. It
  /// is removed once the label is encountered and the jump is valid.
  label_referencest label_references;

  // High level checks

  /// Performs a typecheck on a function declaration inside of the parse tree
  /// and adds symbols for it and its parameters to the symbol table.
  /// \param function: Function to be checked.
  void typecheck_function_declaration(
    const statement_list_parse_treet::functiont &function);

  /// Performs a typecheck on a function block declaration inside of the parse
  /// tree and adds symbols for it and its parameters to the symbol table.
  /// \param function_block: Function block to be checked.
  void typecheck_function_block_declaration(
    const statement_list_parse_treet::function_blockt &function_block);

  /// Performs a typecheck on the tag list of the referenced parse tree and
  /// adds symbols for its contents to the symbol table.
  void typecheck_tag_list();

  /// Adds a symbol for the RLO to the symbol table. This symbol is used by
  /// other operations to save intermediate results of the rlo expression.
  void add_temp_rlo();

  /// Creates a data block type for the given function block.
  /// \param function_block: Function block with an interface that should be
  /// converted to a data block.
  /// \return A type representation of an instance data block for the
  ///   function block.
  struct_typet create_instance_data_block_type(
    const statement_list_parse_treet::function_blockt &function_block);

  /// Performs a typecheck on a variable declaration list and saves the result
  /// to the given component element.
  /// \param var_decls: List of declarations which should be typechecked.
  /// \param [out] components: List of typechecked and converted declarations.
  /// \param var_property: Type of variable declaration list (for example
  ///   input, output, ...).
  void typecheck_function_block_var_decls(
    const statement_list_parse_treet::var_declarationst &var_decls,
    struct_union_typet::componentst &components,
    const irep_idt &var_property);

  /// Performs a typecheck on a variable declaration list and saves the result
  /// to the given component element.
  /// \param var_decls: List of declarations which should be typechecked.
  /// \param [out] params: List of typechecked and converted declarations.
  /// \param function_name: Function to which the variable list belongs (used
  ///   for naming).
  /// \param var_property: Type of variable declaration list (for example
  ///   input, output, ...).
  void typecheck_function_var_decls(
    const statement_list_parse_treet::var_declarationst &var_decls,
    code_typet::parameterst &params,
    const irep_idt &function_name,
    const irep_idt &var_property);

  /// Performs a typecheck on the temp variables of a TIA module and saves the
  /// result to the given symbol value.
  /// \param tia_module: Element whose temp declarations should be checked.
  /// \param [out] tia_symbol: Symbol representation of the TIA module.
  void typecheck_temp_var_decls(
    const statement_list_parse_treet::tia_modulet &tia_module,
    symbolt &tia_symbol);

  /// Performs a typecheck on the networks of a TIA module and saves the
  /// result to the given symbol.
  /// \param tia_module: Module containing the networks that shall be checked.
  /// \param [out] tia_symbol: Symbol representation of the given TIA module.
  void typecheck_statement_list_networks(
    const statement_list_parse_treet::tia_modulet &tia_module,
    symbolt &tia_symbol);

  /// Checks if all jumps reference labels that exist.
  void typecheck_label_references();

  /// Performs a typecheck on a single instruction and saves the result to the
  /// given symbol body if necessary.
  /// \param instruction: Instruction that should be checked.
  /// \param [out] tia_element: Symbol representation of the TIA module.
  void typecheck_statement_list_instruction(
    const statement_list_parse_treet::instructiont &instruction,
    symbolt &tia_element);

  /// Performs a typecheck for the specified instruction in code form.
  /// \param instruction: Code to check.
  /// \param [out] tia_element: Symbol representation of the TIA module.
  void typecheck_code(const codet &instruction, symbolt &tia_element);

  /// Performs a typecheck for the given label in code form.
  /// \param instruction: Label to check.
  /// \param [out] tia_element: Symbol representation of the TIA module.
  void typecheck_label(const codet &instruction, symbolt &tia_element);

  // Load and Transfer instructions

  /// Performs a typecheck on a STL load instruction. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_load(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL transfer instruction and saves the result
  /// to the given symbol. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void
  typecheck_statement_list_transfer(const codet &op_code, symbolt &tia_element);

  // Arithmetic accumulator instructions (int)

  /// Performs a typecheck on a STL accumulator add instruction for integers.
  /// Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_add(const codet &op_code);

  /// Performs a typecheck on a STL accumulator subtract instruction for
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_sub(const codet &op_code);

  /// Performs a typecheck on a STL accumulator divide instruction for
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_div(const codet &op_code);

  /// Performs a typecheck on a STL accumulator multiply instruction for
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_mul(const codet &op_code);

  /// Performs a typecheck on a STL accumulator equality comparison instruction
  /// for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_eq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator inequality comparison
  /// instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_neq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than comparison
  /// instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_gt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than comparison
  /// instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_lt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than or equal
  /// comparison instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_gte(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than or equal comparison
  /// instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_lte(const codet &op_code);

  // Arithmetic accumulator instructions (dint)

  /// Performs a typecheck on a STL accumulator add instruction for double
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_add(const codet &op_code);

  /// Performs a typecheck on a STL accumulator subtract instruction for double
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_sub(const codet &op_code);

  /// Performs a typecheck on a STL accumulator divide instruction for double
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_div(const codet &op_code);

  /// Performs a typecheck on a STL accumulator divide instruction for double
  /// integers. Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_mul(const codet &op_code);

  /// Performs a typecheck on a STL accumulator equality comparison instruction
  /// for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_eq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator inequality comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_neq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_gt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_lt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than or equal
  /// comparison instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_gte(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than or equal
  /// comparison instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_lte(const codet &op_code);

  // Arithmetic accumulator instructions (real)

  /// Performs a typecheck on a STL accumulator add instruction for reals.
  /// Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_add(const codet &op_code);

  /// Performs a typecheck on a STL accumulator subtract instruction for reals.
  /// Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_sub(const codet &op_code);

  /// Performs a typecheck on a STL accumulator divide instruction for reals.
  /// Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_div(const codet &op_code);

  /// Performs a typecheck on a STL accumulator multiply instruction for reals.
  /// Modifies the accumulator.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_mul(const codet &op_code);

  /// Performs a typecheck on a STL accumulator equality comparison instruction
  /// for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_eq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator inequality comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_neq(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_gt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than comparison
  /// instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_lt(const codet &op_code);

  /// Performs a typecheck on a STL accumulator greater than or equal
  /// comparison instruction for double integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_gte(const codet &op_code);

  /// Performs a typecheck on a STL accumulator less than or equal comparison
  /// instruction for integers. Modifies the RLO.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_lte(const codet &op_code);

  // Bit Logic instructions

  /// Performs a typecheck on a STL boolean NOT instruction. Reads and modifies
  /// the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_not(const codet &op_code);

  /// Performs a typecheck on a STL boolean And instruction. Reads and modifies
  /// the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_and(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL boolean Or instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void
  typecheck_statement_list_or(const codet &op_code, const symbolt &tia_element);

  /// Performs a typecheck on a STL boolean XOR instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_xor(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL boolean And Not instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_and_not(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL boolean Or Not instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_or_not(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL boolean XOR Not instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_xor_not(
    const codet &op_code,
    const symbolt &tia_element);

  /// Performs a typecheck on a STL operand-less Or instruction. Reads and
  /// modifies the RLO, OR and FC bit.
  void typecheck_statement_list_and_before_or();

  /// Performs a typecheck on a nested And instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_and(const codet &op_code);

  /// Performs a typecheck on a nested Or instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_or(const codet &op_code);

  /// Performs a typecheck on a nested XOR instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_xor(const codet &op_code);

  /// Performs a typecheck on a nested And Not instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_and_not(const codet &op_code);

  /// Performs a typecheck on a nested Or Not instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_or_not(const codet &op_code);

  /// Performs a typecheck on a nested XOR Not instruction. Pushes the current
  /// program state to the nesting stack and cleans the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nested_xor_not(const codet &op_code);

  /// Performs a typecheck on a Nesting Closed instruction. Uses the latest
  /// entry on the nesting stack and modifies the RLO, OR and FC bit according
  /// to the instruction that started the nesting.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_nesting_closed(const codet &op_code);

  /// Performs a typecheck on a STL assign instruction and saves the result
  /// to the given symbol. Modifies the RLO, OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void
  typecheck_statement_list_assign(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a STL 'SET' instruction and modifies the RLO, OR
  /// and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_set_rlo(const codet &op_code);

  /// Performs a typecheck on a STL 'CLR' instruction and modifies the RLO, OR
  /// and FC bit.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_clr_rlo(const codet &op_code);

  /// Performs a typecheck on a STL 'S' instruction and saves the result
  /// to the given symbol. Modifies the OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_set(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a STL 'R' instruction and saves the result
  /// to the given symbol. Modifies the OR and FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void
  typecheck_statement_list_reset(const codet &op_code, symbolt &tia_element);

  // Program Control instructions

  /// Performs a typecheck on a STL Call instruction and saves the result
  /// to the given symbol. Modifies the OR and /FC bit.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void
  typecheck_statement_list_call(const codet &op_code, symbolt &tia_element);

  // Logic Control instructions

  /// Performs a typecheck on an unconditional jump instruction (JU) and adds
  /// the jump to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_jump_unconditional(
    const codet &op_code,
    symbolt &tia_element);

  /// Performs a typecheck on a conditional jump instruction (JC) and adds it
  /// to the given symbol. Modifies the /FC, RLO and OR bits.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_jump_conditional(
    const codet &op_code,
    symbolt &tia_element);

  /// Performs a typecheck on a inverted conditional jump instruction (JCN) and
  /// adds it to the given symbol. Modifies the /FC, RLO and OR bits.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_statement_list_jump_conditional_not(
    const codet &op_code,
    symbolt &tia_element);

  // Low level checks

  /// Converts the properties of the current typecheck state to a label
  /// location.
  /// \param label: Label to check the properties for.
  /// \return Encoded location information for the given label.
  stl_label_locationt typecheck_label_location(const code_labelt &label);

  /// Performs a typecheck on all references for the given label.
  /// \param label: Label to check.
  /// \param location: Data about the location of the label.
  void typecheck_jump_locations(
    const code_labelt &label,
    const stl_label_locationt &location);

  /// Performs a typecheck on a STL Accumulator instruction for integers.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_int_arith(const codet &op_code);

  /// Performs a typecheck on a STL Accumulator instruction for double
  /// integers.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_dint_arith(const codet &op_code);

  /// Performs a typecheck on a STL Accumulator instruction for reals.
  /// \param op_code: OP code of the instruction.
  void typecheck_statement_list_accu_real_arith(const codet &op_code);

  /// Performs a typecheck on a STL instruction with an additional operand that
  /// should be no constant.
  /// \param op_code: OP code of the instruction.
  /// \return Reference to the operand.
  const symbol_exprt &
  typecheck_instruction_with_non_const_operand(const codet &op_code);

  /// Performs a typecheck on an operand-less STL instruction.
  /// \param op_code: OP code of the instruction.
  void typecheck_instruction_without_operand(const codet &op_code);

  /// Performs a typecheck on a STL instruction that uses two accumulator
  /// entries.
  /// \param op_code: OP code of the instruction.
  void typecheck_binary_accumulator_instruction(const codet &op_code);

  /// Performs a typecheck on a STL instruction that initializes a new boolean
  /// nesting.
  /// \param op_code: OP code of the instruction.
  /// \param rlo_value: Value of the RLO that is pushed on the nesting stack
  ///   for the case that this is the first instruction of a new bit string.
  void typecheck_nested_boolean_instruction(
    const codet &op_code,
    const exprt &rlo_value);

  /// Performs a typecheck on the operand of a not nested boolean instruction
  /// and returns the result.
  /// \param op_code: OP code of the instruction.
  /// \param tia_element: Symbol representation of the TIA element.
  /// \param negate: Whether the operand should be negated (e.g. for the
  ///   `AND NOT` expression).
  /// \return Typechecked operand.
  exprt typecheck_simple_boolean_instruction_operand(
    const codet &op_code,
    const symbolt &tia_element,
    bool negate);

  /// Performs a typecheck on an STL comparison instruction. Modifies the RLO.
  /// \param comparison: ID of the compare expression that should be pushed to
  ///   the RLO.
  void typecheck_accumulator_compare_instruction(const irep_idt &comparison);

  /// Checks if the given label is already present and compares the current
  /// state with it. If there is no entry for the label, a new jump location
  /// is added to the typecheck for later verification.
  /// \param label: Label to check.
  /// \param sets_fc_false: Whether the encountered jump instruction sets the
  ///   /FC bit to false.
  void typecheck_label_reference(const irep_idt &label, bool sets_fc_false);

  /// Performs a typecheck on the given identifier and returns its symbol.
  /// \param identifier: Identifier that should be checked.
  /// \param tia_element: Symbol representation of the current TIA module.
  /// \return Expression including the symbol's name and type.
  exprt
  typecheck_identifier(const symbolt &tia_element, const irep_idt &identifier);

  /// Performs a typecheck on a call of __CPOVER_ASSERT and saves the result
  /// to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_CPROVER_assert(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a call of __CPOVER_ASSUME and saves the result
  /// to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_CPROVER_assume(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a call of a TIA element and saves the result
  /// to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_called_tia_element(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a call of a TIA function and saves the result
  /// to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void typecheck_called_function(const codet &op_code, symbolt &tia_element);

  /// Performs a typecheck on a call of a TIA function block and saves the
  /// result to the given symbol.
  /// \param op_code: OP code of the instruction.
  /// \param [out] tia_element: Symbol representation of the TIA element.
  void
  typecheck_called_function_block(const codet &op_code, symbolt &tia_element);

  /// Checks if the given parameter is inside of the assignment list of a
  /// function call and returns the expression of the assigned variable.
  /// \param assignments: Assignment list of the function call.
  /// \param param: Parameter that should be checked.
  /// \param tia_element: Symbol representation of the TIA element.
  /// \return Expression including the assigned symbol's name and type.
  exprt typecheck_function_call_arguments(
    const std::vector<code_frontend_assignt> &assignments,
    const code_typet::parametert &param,
    const symbolt &tia_element);

  /// Checks if the given assigned expression is a variable or a constant and
  /// returns the typechecked version.
  /// \param tia_element: Symbol representation of the TIA element.
  /// \param rhs: Expression that the function parameter got assigned to.
  /// \return Expression of either a symbol or a constant.
  exprt typecheck_function_call_argument_rhs(
    const symbolt &tia_element,
    const exprt &rhs);

  /// Checks if there is a return value assignment inside of the assignment
  /// list of a function call and returns the expression of the assigned
  /// variable.
  /// \param assignments: Assignment list of the function call.
  /// \param return_type: Type of the return value.
  /// \param tia_element: Symbol representation of the TIA element.
  /// \return Expression including the assigned symbol's name and type.
  exprt typecheck_return_value_assignment(
    const std::vector<code_frontend_assignt> &assignments,
    const typet &return_type,
    const symbolt &tia_element);

  // Helper functions

  /// Adds the given expression to the operands of the Or expression that is
  /// saved in the RLO.
  /// \param op: Operand to be added to the Or instruction.
  void add_to_or_rlo_wrapper(const exprt &op);

  /// Initializes the FC, RLO an OR bits for the scenario when a new boolean
  /// instruction was encontered.
  /// \param op: Operand of the encountered instruction.
  void initialize_bit_expression(const exprt &op);

  /// Modifies the state of the typecheck to resemble the beginning of a new
  /// module. All changes to the implicit typecheck fields are close to the
  /// original TIA behaviour.
  void clear_module_state();

  /// Modifies the state of the typecheck to resemble the beginning of a new
  /// network. All changes to the implicit typecheck fields are close to the
  /// original TIA behaviour.
  void clear_network_state();

  /// Saves the current RLO bit to a temporary variable to prevent false
  /// overrides when modifying boolean variables.
  /// \param tia_element: Symbol representation of the TIA element.
  void save_rlo_state(symbolt &tia_element);
};

#endif // CPROVER_STATEMENT_LIST_STATEMENT_LIST_TYPECHECK_H
