/*******************************************************************\

Module: Java string library preprocess.
        Test for converting an expression to a string expression.

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_root_class.h>

#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_object_factory.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <regex>

SCENARIO(
  "Generate string object",
  "[core][java_bytecode][java_object_factor][gen_nondet_string_init]")
{
  GIVEN("an expression, a location, and a symbol table")
  {
    source_locationt loc;
    symbol_tablet symbol_table;
    register_language(new_java_bytecode_language);

    // Add java.lang.Object to symbol table
    java_class_typet jlo_class_type;
    jlo_class_type.set_tag("java.lang.Object");
    jlo_class_type.set_name("java::java.lang.Object");
    type_symbolt jlo_sym{"java::java.lang.Object", jlo_class_type, ID_java};
    java_root_class(jlo_sym);
    bool failed = symbol_table.add(jlo_sym);
    CHECK_RETURN(!failed);

    // Add java.lang.String to symbol table
    java_string_library_preprocesst preprocess;
    preprocess.initialize_known_type_table();
    preprocess.add_string_type("java.lang.String", symbol_table);
    namespacet ns(symbol_table);

    // Declare a String named arg
    struct_tag_typet java_string_type("java::java.lang.String");
    symbol_exprt expr("arg", java_string_type);

    java_object_factory_parameterst object_factory_parameters;
    object_factory_parameters.max_nondet_string_length = 20;
    object_factory_parameters.function_id = "test";

    WHEN("Initialisation code for a string is generated")
    {
      code_blockt code;
      gen_nondet_init(
        expr,
        code,
        symbol_table,
        loc,
        false,
        lifetimet::DYNAMIC,
        object_factory_parameters,
        update_in_placet::NO_UPDATE_IN_PLACE,
        null_message_handler);

      THEN("Code is produced")
      {
        std::vector<std::string> code_string;

        const std::regex spaces("\\s+");
        const std::regex numbers("\\$[0-9]*");
        for(auto op : code.operands())
        {
          const std::string line = from_expr(ns, "arg", op);
          code_string.push_back(
            std::regex_replace(
              std::regex_replace(line, spaces, " "), numbers, ""));
        }

        // clang-format off
        // NOLINTNEXTLINE
        const std::vector<std::string> reference_code = {
          "int tmp_object_factory;",
          "tmp_object_factory = NONDET(int);",
          CPROVER_PREFIX "assume(tmp_object_factory >= 0);",
          CPROVER_PREFIX "assume(tmp_object_factory <= 20);",
          "char (*nondet_infinite_array_pointer)[INFINITY()];",
          "nondet_infinite_array_pointer = "
            "ALLOCATE(char [INFINITY()], INFINITY(), false);",
          "*nondet_infinite_array_pointer = NONDET(char [INFINITY()]);",
          "int return_array;",
          "return_array = cprover_associate_array_to_pointer_func"
            "(*nondet_infinite_array_pointer, *nondet_infinite_array_pointer);",
          "int return_array;",
          "return_array = cprover_associate_length_to_array_func"
            "(*nondet_infinite_array_pointer, tmp_object_factory);",
          "arg = { .@java.lang.Object={ .@class_identifier"
            "=\"java::java.lang.String\" },"
            " .length=tmp_object_factory, "
            ".data=*nondet_infinite_array_pointer };"};
        // clang-format on

        for(std::size_t i = 0;
            i < code_string.size() && i < reference_code.size();
            ++i)
          REQUIRE(code_string[i] == reference_code[i]);

        REQUIRE(code_string.size() == reference_code.size());
      }
    }
  }
}
