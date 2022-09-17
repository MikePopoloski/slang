# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  unittests
  AssertionTests.cpp
  ClassTests.cpp
  CoverTests.cpp
  DriverTests.cpp
  DiagnosticTests.cpp
  EvalTests.cpp
  ExpressionParsingTests.cpp
  ExpressionTests.cpp
  FileTests.cpp
  HierarchyTests.cpp
  LexerTests.cpp
  LookupTests.cpp
  main.cpp
  MemberParsingTests.cpp
  MemberTests.cpp
  NumericTests.cpp
  PortTests.cpp
  PreprocessorTests.cpp
  StatementParsingTests.cpp
  StatementTests.cpp
  SystemFuncTests.cpp
  Test.cpp
  TypeTests.cpp
  UtilTests.cpp
  VisitorTests.cpp)

target_link_libraries(unittests PRIVATE slang Catch2::Catch2 fmt::fmt)
target_compile_definitions(unittests PRIVATE UNITTESTS)

if(SLANG_CI_BUILD)
  message("Running CI build")
  target_compile_definitions(unittests PRIVATE CI_BUILD)
endif()

# Copy the data directory for running tests from the build folder.
add_custom_command(
  TARGET unittests
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_SOURCE_DIR}/data
          ${CMAKE_CURRENT_BINARY_DIR}/data)

add_test(NAME unittests COMMAND unittests)
set_tests_properties(unittests PROPERTIES TIMEOUT 30)
