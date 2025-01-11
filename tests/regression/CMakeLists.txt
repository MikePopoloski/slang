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
