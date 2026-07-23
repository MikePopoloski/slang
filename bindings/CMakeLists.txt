# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

# Locate nanobind. Prefer a nanobind installed in the active Python environment
# (this is how scikit-build-core provides it during a wheel build); otherwise
# fall back to fetching it from GitHub.
if(NOT nanobind_FOUND)
  execute_process(
    COMMAND "${Python_EXECUTABLE}" -m nanobind --cmake_dir
    OUTPUT_STRIP_TRAILING_WHITESPACE
    OUTPUT_VARIABLE nanobind_cmake_dir
    RESULT_VARIABLE nanobind_result
    ERROR_QUIET)
  if(nanobind_result EQUAL 0 AND EXISTS "${nanobind_cmake_dir}")
    list(APPEND CMAKE_PREFIX_PATH "${nanobind_cmake_dir}")
    find_package(nanobind CONFIG REQUIRED)
    message(STATUS "Using nanobind from Python environment: ${nanobind_cmake_dir}")
  else()
    FetchContent_Declare(
      nanobind
      GIT_REPOSITORY https://github.com/wjakob/nanobind.git
      GIT_TAG v2.13.0
      GIT_SHALLOW ON
      FIND_PACKAGE_ARGS)
    FetchContent_MakeAvailable(nanobind)
    message(STATUS "Using remote nanobind library")
  endif()
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

# Add the pyslang module via nanobind
nanobind_add_module(
  pyslang
  NB_STATIC
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
target_link_libraries(pyslang PRIVATE fmt::fmt)
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

# Generate a Python stub (.pyi) for the compiled module using nanobind's
# built-in stub generator, then install it alongside the module.
nanobind_add_stub(
  pyslang_stub
  MODULE pyslang
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/pyslang.pyi
  PYTHON_PATH $<TARGET_FILE_DIR:pyslang>
  DEPENDS pyslang)

install(
  FILES ${CMAKE_CURRENT_BINARY_DIR}/pyslang.pyi
  COMPONENT pylib
  DESTINATION .)
