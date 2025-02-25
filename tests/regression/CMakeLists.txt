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
