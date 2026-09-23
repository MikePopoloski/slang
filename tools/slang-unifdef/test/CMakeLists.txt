# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_test(
  NAME slang_unifdef_lit_tests
  COMMAND
    ${Python_EXECUTABLE} ${PROJECT_SOURCE_DIR}/scripts/slang-lit.py
    ${CMAKE_CURRENT_LIST_DIR} --slang $<TARGET_FILE:slang::driver> --tool
    unifdef=$<TARGET_FILE:slang_unifdef>)

add_test(NAME slang_unifdef_newline_tests
         COMMAND ${Python_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/newline-test.py
                 ${CMAKE_TEST_LAUNCHER} $<TARGET_FILE:slang_unifdef>)
