# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "3.0.0")
endif()

FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG v3.3.2
  GIT_SHALLOW ON
  ${find_pkg_args})
FetchContent_MakeAvailable(Catch2)

if(Catch2_FOUND)
  get_target_property(Catch2_INCLUDE_DIR Catch2::Catch2
                      INTERFACE_INCLUDE_DIRECTORIES)
  message(STATUS "Found system Catch2 version: ${Catch2_VERSION}")
  message(STATUS "Using system Catch2 include: ${Catch2_INCLUDE_DIR}")
else()
  message(STATUS "Using remote Catch2 library")
endif()

add_executable(
  unittests
  unittests/AssertionTests.cpp
  unittests/ClassTests.cpp
  unittests/CommandLineTests.cpp
  unittests/CoverTests.cpp
  unittests/DriverTests.cpp
  unittests/DiagnosticTests.cpp
  unittests/EvalTests.cpp
  unittests/ExpressionParsingTests.cpp
  unittests/ExpressionTests.cpp
  unittests/FileTests.cpp
  unittests/HierarchyTests.cpp
  unittests/IntervalMapTests.cpp
  unittests/LexerTests.cpp
  unittests/LookupTests.cpp
  unittests/main.cpp
  unittests/MemberParsingTests.cpp
  unittests/MemberTests.cpp
  unittests/NumericTests.cpp
  unittests/PortTests.cpp
  unittests/PreprocessorTests.cpp
  unittests/StatementParsingTests.cpp
  unittests/StatementTests.cpp
  unittests/SystemFuncTests.cpp
  unittests/Test.cpp
  unittests/TypeTests.cpp
  unittests/VisitorTests.cpp
  unittests/WarningTests.cpp)

target_link_libraries(
  unittests
  PRIVATE slang::slang Catch2::Catch2 fmt::fmt
  PUBLIC ${SLANG_LIBRARIES})
target_compile_definitions(unittests PRIVATE UNITTESTS)

if(SLANG_CI_BUILD)
  message("Running CI build")
  target_compile_definitions(unittests PRIVATE CI_BUILD)
endif()

# Copy the data directory for running tests from the build folder.
add_custom_command(
  TARGET unittests
  POST_BUILD
  COMMAND
    ${CMAKE_COMMAND} -E copy_directory
    ${CMAKE_CURRENT_SOURCE_DIR}/unittests/data
    ${CMAKE_CURRENT_BINARY_DIR}/unittests/data)

add_test(NAME unittests COMMAND unittests)
set_tests_properties(unittests PROPERTIES TIMEOUT 60)

add_test(NAME regression_delayed_reg
         COMMAND slang::driver
                 "${CMAKE_CURRENT_LIST_DIR}/regression/delayed_reg.v")
add_test(NAME regression_wire_module
         COMMAND slang::driver
                 "${CMAKE_CURRENT_LIST_DIR}/regression/wire_module.v")
