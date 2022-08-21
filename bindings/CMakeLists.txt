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
  python/binding.cpp
  python/compilation.cpp
  python/numeric.cpp
  python/pyslang.cpp
  python/symbols.cpp
  python/syntax.cpp
  python/types.cpp
  python/util.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings.cpp)
target_link_libraries(pyslang PUBLIC slangcompiler)
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
