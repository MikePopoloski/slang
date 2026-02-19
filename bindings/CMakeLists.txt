# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "3.0")
endif()

FetchContent_Declare(
  pybind11
  GIT_REPOSITORY https://github.com/pybind/pybind11.git
  GIT_TAG v3.0.2
  GIT_SHALLOW ON
  ${find_pkg_args})
FetchContent_MakeAvailable(pybind11)

if(pybind11_FOUND)
  message(STATUS "Using system pybind11 library: ${pybind11_VERSION}")
  message(STATUS "Using system pybind11 include: ${pybind11_INCLUDE_DIRS}")
else()
  message(STATUS "Using remote pybind11 library")
endif()

# Generate bindings for syntax node types and SyntaxFactory
add_custom_command(
  COMMAND
    ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
    ${CMAKE_CURRENT_BINARY_DIR} --python-bindings --syntax
    ${SCRIPTS_DIR}/syntax.txt
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings0.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings1.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings2.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings3.cpp
         ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxFactory.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
  COMMENT "Generating syntax bindings")

# Add the pyslang module via pybind11
pybind11_add_module(
  pyslang
  MODULE
  python/AnalysisBindings.cpp
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
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings3.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxFactory.cpp)
set_source_files_properties(
  python/pyslang.cpp PROPERTIES COMPILE_DEFINITIONS
                                VERSION_INFO=${PROJECT_VERSION})
target_link_libraries(pyslang PUBLIC slang::slang)
target_include_directories(pyslang PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/python)

install(
  TARGETS pyslang
  COMPONENT pylib
  DESTINATION .)

# Install py.typed marker file for PEP 561 compliance
install(
  FILES ${CMAKE_CURRENT_SOURCE_DIR}/../pyslang/pyslang/py.typed
        ${CMAKE_CURRENT_SOURCE_DIR}/../pyslang/pyslang/__init__.py
  COMPONENT pylib
  DESTINATION .)

# Generate Python stubs as a post-install step
install(
  CODE "
  set(STUBGEN_PYTHON_EXECUTABLE \"${Python_EXECUTABLE}\")
  # Do NOT override CMAKE_INSTALL_PREFIX - the install-time value is correct
  include(\"${CMAKE_CURRENT_SOURCE_DIR}/generate_stubs.cmake\")
"
  COMPONENT pylib)
