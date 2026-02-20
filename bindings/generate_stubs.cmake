# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

message(STATUS "Generating Python stubs for pyslang...")

if(NOT DEFINED STUBGEN_PYTHON_EXECUTABLE)
  find_package(
    Python
    COMPONENTS Interpreter
    REQUIRED)
  set(STUBGEN_PYTHON_EXECUTABLE "${Python_EXECUTABLE}")
endif()

message(STATUS "Using Python: ${STUBGEN_PYTHON_EXECUTABLE}")

if(DEFINED ENV{DESTDIR})
  set(INSTALL_DIR "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}")
else()
  set(INSTALL_DIR "${CMAKE_INSTALL_PREFIX}")
endif()

message(STATUS "Install directory: ${INSTALL_DIR}")

# ---------------------------------------------------------------------------
# Diagnostic: verify the extension is actually here
# ---------------------------------------------------------------------------
file(GLOB EXT_FILES "${INSTALL_DIR}/pyslang.*" "${INSTALL_DIR}/pyslang.*.so"
     "${INSTALL_DIR}/pyslang.*.pyd")
message(STATUS "Extension files found: ${EXT_FILES}")

if(NOT EXT_FILES)
  message(WARNING "No C extension found at ${INSTALL_DIR}/pyslang.* "
                  "— is the target installed before this script runs?")
  return()
endif()

if(NOT EXISTS "${INSTALL_DIR}/__init__.py")
  message(WARNING "__init__.py not found at ${INSTALL_DIR}/ "
                  "— is it installed before this script runs?")
  return()
endif()

# ---------------------------------------------------------------------------
# Step 1: Create a temporary importable package structure
#
# The install layout is flat (DESTINATION .), so files are directly in
# INSTALL_DIR. Python needs a parent directory with a pyslang/ subdirectory to
# resolve "import pyslang.pyslang". We create a temporary symlink/copy.
# ---------------------------------------------------------------------------
set(STUBGEN_TMPDIR "${INSTALL_DIR}/_stubgen_tmp")
set(STUBGEN_PKGDIR "${STUBGEN_TMPDIR}/pyslang")

# Clean up any previous run
file(REMOVE_RECURSE "${STUBGEN_TMPDIR}")
file(MAKE_DIRECTORY "${STUBGEN_TMPDIR}")

# Create a symlink (or copy on Windows) so that _stubgen_tmp/pyslang/ ->
# ${INSTALL_DIR}/ which gives us _stubgen_tmp/pyslang/__init__.py, etc.
if(WIN32)
  # Windows: copy instead of symlink (symlinks need admin on some configs)
  file(
    COPY "${INSTALL_DIR}/"
    DESTINATION "${STUBGEN_PKGDIR}"
    PATTERN "_stubgen_tmp" EXCLUDE)
else()
  file(CREATE_LINK "${INSTALL_DIR}" "${STUBGEN_PKGDIR}" SYMBOLIC)
endif()

# Verify the structure
message(STATUS "Temp package dir: ${STUBGEN_PKGDIR}")
execute_process(
  COMMAND
    ${STUBGEN_PYTHON_EXECUTABLE} -c
    "import sys; sys.path.insert(0, '${STUBGEN_TMPDIR}'); import pyslang.pyslang; print('Import OK')"
  RESULT_VARIABLE IMPORT_RESULT
  OUTPUT_VARIABLE IMPORT_OUTPUT
  ERROR_VARIABLE IMPORT_ERROR)

if(NOT IMPORT_RESULT EQUAL 0)
  message(
    WARNING "Cannot import pyslang.pyslang from temp structure: ${IMPORT_ERROR}"
  )
  file(REMOVE_RECURSE "${STUBGEN_TMPDIR}")
  return()
endif()
message(STATUS "Import test passed: ${IMPORT_OUTPUT}")

# ---------------------------------------------------------------------------
# Step 2: Ensure pybind11-stubgen is available
# ---------------------------------------------------------------------------
execute_process(
  COMMAND ${STUBGEN_PYTHON_EXECUTABLE} -c "import pybind11_stubgen"
  RESULT_VARIABLE STUBGEN_CHECK
  OUTPUT_QUIET ERROR_QUIET)

if(NOT STUBGEN_CHECK EQUAL 0)
  message(STATUS "Installing pybind11-stubgen...")
  execute_process(
    COMMAND ${STUBGEN_PYTHON_EXECUTABLE} -m pip install pybind11-stubgen
    RESULT_VARIABLE PIP_RESULT
    OUTPUT_QUIET ERROR_QUIET)
  if(NOT PIP_RESULT EQUAL 0)
    message(WARNING "Failed to install pybind11-stubgen")
    file(REMOVE_RECURSE "${STUBGEN_TMPDIR}")
    return()
  endif()
endif()

# ---------------------------------------------------------------------------
# Step 3: Set library search paths for shared library dependencies
# ---------------------------------------------------------------------------
if(APPLE)
  if(DEFINED ENV{DYLD_LIBRARY_PATH})
    set(ENV{DYLD_LIBRARY_PATH} "${INSTALL_DIR}/../lib:$ENV{DYLD_LIBRARY_PATH}")
  else()
    set(ENV{DYLD_LIBRARY_PATH} "${INSTALL_DIR}/../lib")
  endif()
elseif(UNIX)
  if(DEFINED ENV{LD_LIBRARY_PATH})
    set(ENV{LD_LIBRARY_PATH} "${INSTALL_DIR}/../lib:$ENV{LD_LIBRARY_PATH}")
  else()
    set(ENV{LD_LIBRARY_PATH} "${INSTALL_DIR}/../lib")
  endif()
endif()

# ---------------------------------------------------------------------------
# Step 4: Generate stubs using the temporary package structure
# ---------------------------------------------------------------------------
# PYTHONPATH points to the temp dir where pyslang/ is a proper package
if(DEFINED ENV{PYTHONPATH})
  set(ENV{PYTHONPATH} "${STUBGEN_TMPDIR}:$ENV{PYTHONPATH}")
else()
  set(ENV{PYTHONPATH} "${STUBGEN_TMPDIR}")
endif()

message(STATUS "Running pybind11-stubgen...")
message(STATUS "  PYTHONPATH = $ENV{PYTHONPATH}")

# Generate stubs into a temporary output directory
set(STUBGEN_OUTDIR "${INSTALL_DIR}/_stubgen_out")
file(REMOVE_RECURSE "${STUBGEN_OUTDIR}")

execute_process(
  COMMAND ${STUBGEN_PYTHON_EXECUTABLE} -m pybind11_stubgen pyslang.pyslang -o
          "${STUBGEN_OUTDIR}" --root-suffix "" --ignore-invalid-expressions=all
  WORKING_DIRECTORY ${STUBGEN_TMPDIR}
  RESULT_VARIABLE STUBGEN_RESULT
  OUTPUT_VARIABLE STUBGEN_OUTPUT
  ERROR_VARIABLE STUBGEN_ERROR)

message(STATUS "stubgen exit code: ${STUBGEN_RESULT}")
message(STATUS "stubgen stdout: ${STUBGEN_OUTPUT}")
message(STATUS "stubgen stderr: ${STUBGEN_ERROR}")

if(NOT STUBGEN_RESULT EQUAL 0)
  message(WARNING "Failed to generate stubs: ${STUBGEN_ERROR}")
  file(REMOVE_RECURSE "${STUBGEN_TMPDIR}" "${STUBGEN_OUTDIR}")
  return()
endif()

# ---------------------------------------------------------------------------
# Step 5: Discover and flatten generated stubs into the install directory
#
# stubgen may produce: _stubgen_out/pyslang/pyslang/__init__.pyi   (submodule
# stubs) _stubgen_out/pyslang/pyslang/ast.pyi OR:
# _stubgen_out/pyslang/pyslang.pyi            (single-file stub)
#
# We need everything to end up flat in INSTALL_DIR (which IS the package).
# ---------------------------------------------------------------------------
message(STATUS "Looking for generated stubs...")
file(GLOB_RECURSE ALL_GENERATED_STUBS "${STUBGEN_OUTDIR}/*.pyi")
message(STATUS "Generated stubs: ${ALL_GENERATED_STUBS}")

set(NESTED_DIR "${STUBGEN_OUTDIR}/pyslang/pyslang")

if(IS_DIRECTORY "${NESTED_DIR}")
  # Submodule stubs: pyslang/pyslang/*.pyi -> INSTALL_DIR/*.pyi
  message(STATUS "Found nested stub directory, flattening...")
  file(GLOB STUB_FILES "${NESTED_DIR}/*.pyi")
  foreach(STUB ${STUB_FILES})
    get_filename_component(STUB_NAME "${STUB}" NAME)
    file(COPY "${STUB}" DESTINATION "${INSTALL_DIR}")
    message(STATUS "  Copied ${STUB_NAME}")
  endforeach()
elseif(EXISTS "${STUBGEN_OUTDIR}/pyslang/pyslang.pyi")
  # Single-file stub
  file(COPY "${STUBGEN_OUTDIR}/pyslang/pyslang.pyi"
       DESTINATION "${INSTALL_DIR}")
  message(STATUS "  Copied pyslang.pyi (single-file stub)")
else()
  message(
    WARNING "No stubs found in expected locations under ${STUBGEN_OUTDIR}")
  file(REMOVE_RECURSE "${STUBGEN_TMPDIR}" "${STUBGEN_OUTDIR}")
  return()
endif()

# ---------------------------------------------------------------------------
# Step 6: Fix internal references  pyslang.pyslang.X -> pyslang.X
# ---------------------------------------------------------------------------
message(STATUS "Fixing internal references in stubs...")
file(GLOB STUB_FILES "${INSTALL_DIR}/*.pyi")
foreach(STUB ${STUB_FILES})
  file(READ "${STUB}" STUB_CONTENT)
  string(REPLACE "pyslang.pyslang" "pyslang" STUB_CONTENT "${STUB_CONTENT}")
  file(WRITE "${STUB}" "${STUB_CONTENT}")
endforeach()

# ---------------------------------------------------------------------------
# Step 7: Create proxy .py files for submodules
# ---------------------------------------------------------------------------
set(SUBMODULES ast syntax parsing analysis driver)

message(STATUS "Creating proxy submodule files...")
foreach(SUB ${SUBMODULES})
  set(PROXY_FILE "${INSTALL_DIR}/${SUB}.py")
  if(NOT EXISTS "${PROXY_FILE}")
    file(WRITE "${PROXY_FILE}"
         "from pyslang.pyslang.${SUB} import *  # noqa: F401,F403\n")
    message(STATUS "  Created ${SUB}.py")
  endif()
endforeach()

# ---------------------------------------------------------------------------
# Step 8: Ensure py.typed marker exists
# ---------------------------------------------------------------------------
if(NOT EXISTS "${INSTALL_DIR}/py.typed")
  file(WRITE "${INSTALL_DIR}/py.typed" "")
  message(STATUS "Created py.typed marker")
endif()

# ---------------------------------------------------------------------------
# Step 9: Clean up temporary directories
# ---------------------------------------------------------------------------
file(REMOVE_RECURSE "${STUBGEN_TMPDIR}" "${STUBGEN_OUTDIR}")
message(STATUS "Cleaned up temporary directories")

# ---------------------------------------------------------------------------
# Step 10: Verify
# ---------------------------------------------------------------------------
message(STATUS "Final contents of ${INSTALL_DIR}:")
file(GLOB FINAL_CONTENTS "${INSTALL_DIR}/*")
foreach(F ${FINAL_CONTENTS})
  get_filename_component(FNAME "${F}" NAME)
  message(STATUS "  ${FNAME}")
endforeach()

message(STATUS "Stub generation complete")
