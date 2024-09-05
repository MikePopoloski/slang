# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

add_executable(
  unittests
  ast/AssertionTests.cpp
  ast/ClassTests.cpp
  ast/ConfigTests.cpp
  ast/CoverTests.cpp
  ast/EvalTests.cpp
  ast/ExpressionTests.cpp
  ast/HierarchyTests.cpp
  ast/InterfaceTests.cpp
  ast/LookupTests.cpp
  ast/MemberTests.cpp
  ast/ParameterTests.cpp
  ast/PortTests.cpp
  ast/PrimitiveTests.cpp
  ast/SerializerTests.cpp
  ast/StatementTests.cpp
  ast/SubroutineTests.cpp
  ast/SystemFuncTests.cpp
  ast/TypeTests.cpp
  ast/WarningTests.cpp
  parsing/DiagnosticTests.cpp
  parsing/ExpressionParsingTests.cpp
  parsing/LexerTests.cpp
  parsing/MemberParsingTests.cpp
  parsing/PreprocessorTests.cpp
  parsing/VisitorTests.cpp
  parsing/StatementParsingTests.cpp
  util/CommandLineTests.cpp
  util/IntervalMapTests.cpp
  util/NumericTests.cpp
  util/SmallVectorTests.cpp
  util/ThreadPoolTests.cpp
  util/UtilTests.cpp
  DriverTests.cpp
  FileTests.cpp
  main.cpp
  Test.cpp)

target_include_directories(unittests PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(unittests PRIVATE slang::slang Catch2::Catch2)
target_compile_definitions(unittests PRIVATE UNITTESTS)

if(SLANG_CI_BUILD)
  message("Running CI build")
  target_compile_definitions(unittests PRIVATE CI_BUILD)
endif()

if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_sources(unittests PRIVATE ${PROJECT_SOURCE_DIR}/scripts/win32.manifest)
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  # Suppress annoying false positive Wstringop-overflow warnings
  target_compile_options(unittests PUBLIC "-Wno-stringop-overflow")
  target_link_options(unittests PUBLIC "-Wno-stringop-overflow")
endif()

# Copy the data directory for running tests from the build folder.
add_custom_command(
  TARGET unittests
  POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_SOURCE_DIR}/data
          ${CMAKE_CURRENT_BINARY_DIR}/data)
add_custom_command(
  TARGET unittests
  POST_BUILD
  COMMAND
    ${CMAKE_COMMAND} -E copy_directory
    ${CMAKE_CURRENT_SOURCE_DIR}/../regression
    ${CMAKE_CURRENT_BINARY_DIR}/../regression)

add_test(NAME unittests COMMAND unittests)
set_tests_properties(unittests PROPERTIES TIMEOUT 60)
