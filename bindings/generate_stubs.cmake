# CMake script to generate Python stubs during installation This runs as a
# post-install step to generate .pyi files

message(STATUS "Generating Python stubs for pyslang...")

# Use the Python executable passed from the parent CMake, or fall back to
# find_package
if(NOT DEFINED STUBGEN_PYTHON_EXECUTABLE)
  message(
    WARNING
      "STUBGEN_PYTHON_EXECUTABLE not set, falling back to find_package(Python)")
  find_package(
    Python
    COMPONENTS Interpreter
    REQUIRED)
  set(STUBGEN_PYTHON_EXECUTABLE "${Python_EXECUTABLE}")
endif()

message(STATUS "Using Python: ${STUBGEN_PYTHON_EXECUTABLE}")

# Check if we're in a wheel build (CMAKE_INSTALL_PREFIX will be set to wheel
# staging directory)
if(DEFINED ENV{DESTDIR})
  set(INSTALL_DIR "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}")
else()
  set(INSTALL_DIR "${CMAKE_INSTALL_PREFIX}")
endif()

message(STATUS "Install directory: ${INSTALL_DIR}")

# Try to check if pybind11-stubgen is available
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
endif()

# Generate stubs - Add install dir to Python path so it can import the module
set(ENV{PYTHONPATH} "${INSTALL_DIR}:$ENV{PYTHONPATH}")

execute_process(
  COMMAND ${STUBGEN_PYTHON_EXECUTABLE} -m pybind11_stubgen pyslang -o
          "${INSTALL_DIR}" --root-suffix ""
  WORKING_DIRECTORY ${INSTALL_DIR}
  RESULT_VARIABLE STUBGEN_RESULT
  OUTPUT_VARIABLE STUBGEN_OUTPUT
  ERROR_VARIABLE STUBGEN_ERROR)

if(STUBGEN_RESULT EQUAL 0)
  message(STATUS "Successfully generated stubs")
  # Verify stub file exists
  if(EXISTS "${INSTALL_DIR}/pyslang/__init__.pyi")
    message(STATUS "Stub file created: ${INSTALL_DIR}/pyslang/__init__.pyi")
  else()
    message(WARNING "Stub file not found after generation")
  endif()
else()
  message(WARNING "Failed to generate stubs: ${STUBGEN_ERROR}")
endif()
