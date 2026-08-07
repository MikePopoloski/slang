# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_test(
  NAME ast_lit_tests
  COMMAND ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/slang-lit.py
          ${CMAKE_CURRENT_LIST_DIR} --slang $<TARGET_FILE:slang::driver>)
