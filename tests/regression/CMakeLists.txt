# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_test(NAME regression_all_file
         COMMAND slang::driver "${CMAKE_CURRENT_LIST_DIR}/all.sv"
                 "--ast-json=-" "--ast-json-detailed-types" "--std=1800-2023")

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
          ${CMAKE_CURRENT_LIST_DIR}/all.sv "--std=1800-2023")

set_tests_properties(regression_cst_json_roundtrip
                     PROPERTIES DEPENDS regression_cst_json_gen)

# CST JSON round trip test focused on preprocessor conditional directives.
add_test(
  NAME regression_cst_json_conditionals_gen
  COMMAND
    slang::driver --cst-json ${CMAKE_CURRENT_BINARY_DIR}/conditionals_cst.json
    ${CMAKE_CURRENT_LIST_DIR}/conditionals.sv "--std=1800-2023")

add_test(
  NAME regression_cst_json_conditionals_roundtrip
  COMMAND
    ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/reconstruct_from_json.py
    ${CMAKE_CURRENT_BINARY_DIR}/conditionals_cst.json --compare
    ${CMAKE_CURRENT_LIST_DIR}/conditionals.sv)

set_tests_properties(regression_cst_json_conditionals_roundtrip
                     PROPERTIES DEPENDS regression_cst_json_conditionals_gen)

# Exercise the same source with different conditional branches enabled. Each
# variant writes to a separate file so that the generation tests can run
# concurrently.
function(add_cst_json_conditionals_variant name)
  set(json_file ${CMAKE_CURRENT_BINARY_DIR}/conditionals_${name}_cst.json)

  add_test(
    NAME regression_cst_json_conditionals_${name}_gen
    COMMAND slang::driver --cst-json ${json_file}
            ${CMAKE_CURRENT_LIST_DIR}/conditionals.sv "--std=1800-2023" ${ARGN})

  add_test(
    NAME regression_cst_json_conditionals_${name}_roundtrip
    COMMAND
      ${Python_EXECUTABLE}
      ${PROJECT_SOURCE_DIR}/scripts/reconstruct_from_json.py ${json_file}
      --compare ${CMAKE_CURRENT_LIST_DIR}/conditionals.sv)

  set_tests_properties(
    regression_cst_json_conditionals_${name}_roundtrip
    PROPERTIES DEPENDS regression_cst_json_conditionals_${name}_gen)
endfunction()

add_cst_json_conditionals_variant(foo -DFOO)
add_cst_json_conditionals_variant(bar_baz -DBAR -DBAZ)
add_cst_json_conditionals_variant(foo_inner -DFOO -DINNER)

add_subdirectory(driver)

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
