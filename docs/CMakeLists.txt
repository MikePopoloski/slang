# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

FetchContent_Declare(
  mcss
  URL https://github.com/MikePopoloski/m.css/releases/download/release-8/mcss.zip
  URL_HASH MD5=39c52acc36aa3a604616f22dc2549ad8
  SOURCE_DIR "${PROJECT_BINARY_DIR}/mcss"
  UPDATE_DISCONNECTED YES)
FetchContent_MakeAvailable(mcss)

# Find all the public headers of the slang project
file(GLOB_RECURSE SLANG_PUBLIC_HEADERS ${PROJECT_SOURCE_DIR}/include/*.h)
file(GLOB_RECURSE SLANG_DOX_FILES ${PROJECT_SOURCE_DIR}/docs/*.dox)

set(DOXYGEN_INPUT_DIR_LIST
    "${PROJECT_SOURCE_DIR}/include"
    "${PROJECT_SOURCE_DIR}/docs"
    "${CMAKE_CURRENT_BINARY_DIR}/"
    "${CMAKE_CURRENT_BINARY_DIR}/../source/slang/syntax"
    "${CMAKE_CURRENT_BINARY_DIR}/../source/slang/parsing")
set(DOXYGEN_EXAMPLE_DIR_LIST
    "${PROJECT_SOURCE_DIR}/tools/hier/README.md"
    "${PROJECT_SOURCE_DIR}/tools/netlist/README.md"
    "${PROJECT_SOURCE_DIR}/tools/reflect/README.md"
    "${PROJECT_SOURCE_DIR}/tools/rewriter/README.md"
    "${PROJECT_SOURCE_DIR}/tools/threadtest/README.md"
    "${PROJECT_SOURCE_DIR}/tools/tidy/README.md")
set(DOXYGEN_EXTERNAL_DIR "${PROJECT_SOURCE_DIR}/external")
set(DOXYGEN_STRIP_PATH "${DOXYGEN_INPUT_DIR}")
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR})
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/html/index.html)
set(DOXYGEN_TAGFILES
    "${CMAKE_CURRENT_SOURCE_DIR}/cppreference-doxygen-web.tag.xml=http://en.cppreference.com/w/"
)
set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
set(SCRIPTS_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../scripts)
set(MCSS_DOXYGENPY_PATH "${mcss_SOURCE_DIR}/documentation/doxygen.py")
set(MCSS_PYTHONPY_PATH "${mcss_SOURCE_DIR}/documentation/python.py")

string(REPLACE ";" " " DOXYGEN_INPUT_DIR "${DOXYGEN_INPUT_DIR_LIST}")
string(REPLACE ";" " " DOXYGEN_EXAMPLE_DIRS "${DOXYGEN_EXAMPLE_DIR_LIST}")

configure_file(${DOXYFILE_IN} ${DOXYFILE_OUT} @ONLY)

add_custom_command(
  COMMAND
    ${Python_EXECUTABLE} ${SCRIPTS_DIR}/diagnostic_gen.py --outDir
    ${CMAKE_CURRENT_BINARY_DIR} --docs --slangBin $<TARGET_FILE:slang::driver>
    --diagnostics ${SCRIPTS_DIR}/diagnostics.txt
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/warnings.dox
  DEPENDS ${SCRIPTS_DIR}/diagnostic_gen.py ${SCRIPTS_DIR}/diagnostics.txt
          ${SCRIPTS_DIR}/warning_docs.txt
  COMMENT "Generating warning docs")

add_custom_command(
  OUTPUT ${DOXYGEN_INDEX_FILE}
  DEPENDS ${SLANG_PUBLIC_HEADERS} ${SLANG_DOX_FILES} ${DOXYGEN_EXAMPLE_DIR_LIST}
          ${CMAKE_CURRENT_BINARY_DIR}/warnings.dox
  COMMAND "${CMAKE_COMMAND}" -E rm -rf ${CMAKE_CURRENT_BINARY_DIR}/html
          ${CMAKE_CURRENT_BINARY_DIR}/xml
  COMMAND ${Python_EXECUTABLE} ${MCSS_DOXYGENPY_PATH} ${DOXYFILE_OUT}
  MAIN_DEPENDENCY ${DOXYFILE_OUT}
  ${DOXYFILE_IN}
  COMMENT "Generating docs"
  VERBATIM)

add_custom_target(docs ALL DEPENDS ${DOXYGEN_INDEX_FILE})

# --- Python documentation with virtual environment ---
set(PYTHON_DOCS_DIR ${CMAKE_CURRENT_BINARY_DIR}/html/pyslang)
set(PYTHON_VENV_DIR ${PROJECT_BINARY_DIR}/venv)

add_custom_command(
  OUTPUT ${PYTHON_DOCS_DIR}/index.html
  COMMAND ${Python_EXECUTABLE} -m venv ${PYTHON_VENV_DIR}
  COMMAND ${PYTHON_VENV_DIR}/bin/python -m pip install --upgrade pip
  COMMAND ${PYTHON_VENV_DIR}/bin/python -m pip install jinja2 pygments docutils
  COMMAND
    ${PYTHON_VENV_DIR}/bin/python -m pip install . -v
    "--config-settings=build-dir=${CMAKE_CURRENT_BINARY_DIR}/../pyslang/{wheel_tag}"
  COMMAND DOC_OUTPUT_DIR=${PYTHON_DOCS_DIR} ${PYTHON_VENV_DIR}/bin/python
          ${MCSS_PYTHONPY_PATH} ${PROJECT_SOURCE_DIR}/pyslang/docs/conf.py
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
  DEPENDS ${PROJECT_SOURCE_DIR}/pyslang/docs/conf.py ${DOXYGEN_INDEX_FILE}
  COMMENT "Generating Python docs in virtual environment"
  VERBATIM)

add_custom_target(python_docs DEPENDS ${PYTHON_DOCS_DIR}/index.html)

# Make sure both docs and python_docs are built with `make docs`
add_dependencies(docs python_docs)
