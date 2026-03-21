# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

if(SLANG_INCLUDE_LLVM)
  add_test(
    NAME codegen_ir_tests
    COMMAND
      ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/slang-lit.py
      ${CMAKE_CURRENT_LIST_DIR} --slang $<TARGET_FILE:slang_driver> --no-color)
endif()
