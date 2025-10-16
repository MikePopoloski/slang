# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_test(NAME regression_delayed_reg
         COMMAND slang::driver "${CMAKE_CURRENT_LIST_DIR}/delayed_reg.v")
add_test(NAME regression_wire_module
         COMMAND slang::driver "${CMAKE_CURRENT_LIST_DIR}/wire_module.v")
add_test(NAME regression_all_file
         COMMAND slang::driver "${CMAKE_CURRENT_LIST_DIR}/all.sv"
                 "--ast-json=-" "--ast-json-detailed-types")

# CST JSON round trip test
add_test(
  NAME regression_cst_json_roundtrip
  COMMAND
    ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/reconstruct_from_json.py
    ${CMAKE_CURRENT_BINARY_DIR}/all_cst.json --compare
    ${CMAKE_CURRENT_LIST_DIR}/all.sv)

# Generate the CST JSON file as a prerequisite
add_test(
  NAME regression_cst_json_gen
  COMMAND slang::driver --cst-json ${CMAKE_CURRENT_BINARY_DIR}/all_cst.json
          ${CMAKE_CURRENT_LIST_DIR}/all.sv)

set_tests_properties(regression_cst_json_roundtrip
                     PROPERTIES DEPENDS regression_cst_json_gen)

if(SLANG_INCLUDE_UVM_TEST)
  FetchContent_Declare(
    uvm
    URL https://github.com/accellera-official/uvm-core/archive/refs/tags/2020.3.1.zip
    URL_HASH MD5=38c2191e13242da4823e00051e406781
    SOURCE_DIR "${CMAKE_CURRENT_BINARY_DIR}/uvm"
    UPDATE_DISCONNECTED YES)
  FetchContent_MakeAvailable(uvm)

  add_test(NAME regression_uvm
           COMMAND slang::driver "${CMAKE_CURRENT_BINARY_DIR}/uvm/src/uvm.sv"
                   "-I" "${CMAKE_CURRENT_BINARY_DIR}/uvm/src")
endif()
