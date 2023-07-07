# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

set(find_pkg_args "")
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL "3.24.0")
  set(find_pkg_args "FIND_PACKAGE_ARGS" "2.10.0")
endif()

FetchContent_Declare(
  pybind11
  GIT_REPOSITORY https://github.com/pybind/pybind11.git
  GIT_TAG v2.10.4
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
  COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
          ${CMAKE_CURRENT_BINARY_DIR} --python-bindings
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
  COMMENT "Generating syntax bindings")

# Add the pyslang module via pybind11
pybind11_add_module(
  pyslang
  MODULE
  python/ASTBindings.cpp
  python/CompBindings.cpp
  python/NumericBindings.cpp
  python/pyslang.cpp
  python/SymbolBindings.cpp
  python/SyntaxBindings.cpp
  python/TypeBindings.cpp
  python/UtilBindings.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings.cpp)
target_link_libraries(pyslang PUBLIC slang::slang)
target_include_directories(pyslang PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/python)
target_compile_definitions(pyslang PRIVATE VERSION_INFO=${PROJECT_VERSION})

install(
  TARGETS pyslang
  COMPONENT pylib
  DESTINATION .)

# Fake install component target to allow installing just a minimal set of things
# when building from Python.
add_custom_target(
  pyslang-install-pylib
  ${CMAKE_COMMAND} -DCMAKE_INSTALL_COMPONENT=pylib -P
  "${PROJECT_BINARY_DIR}/cmake_install.cmake"
  DEPENDS pyslang)
