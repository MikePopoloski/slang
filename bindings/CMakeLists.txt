# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "2.13.1")
endif()

FetchContent_Declare(
  pybind11
  GIT_REPOSITORY https://github.com/pybind/pybind11.git
  GIT_TAG v2.13.6
  GIT_SHALLOW ON
  ${find_pkg_args})
FetchContent_MakeAvailable(pybind11)

if(pybind11_FOUND)
  message(STATUS "Using system pybind11 library: ${pybind11_VERSION}")
  message(STATUS "Using system pybind11 include: ${pybind11_INCLUDE_DIRS}")
else()
  message(STATUS "Using remote pybind11 library")
endif()

# Generate bindings for syntax node types
add_custom_command(
  COMMAND
    ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
    ${CMAKE_CURRENT_BINARY_DIR} --python-bindings --syntax
    ${SCRIPTS_DIR}/syntax.txt
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings0.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings1.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings2.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings3.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
  COMMENT "Generating syntax bindings")

# Add the pyslang module via pybind11
pybind11_add_module(
  pyslang
  MODULE
  python/ASTBindings.cpp
  python/CompBindings.cpp
  python/ExpressionBindings.cpp
  python/NumericBindings.cpp
  python/pyslang.cpp
  python/StatementBindings.cpp
  python/SymbolBindings.cpp
  python/SyntaxBindings.cpp
  python/TypeBindings.cpp
  python/UtilBindings.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings0.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings1.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings2.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings3.cpp)
set_source_files_properties(
  python/pyslang.cpp PROPERTIES COMPILE_DEFINITIONS
                                VERSION_INFO=${PROJECT_VERSION})
target_link_libraries(pyslang PUBLIC slang::slang)
target_include_directories(pyslang PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/python)

install(
  TARGETS pyslang
  COMPONENT pylib
  DESTINATION .)
