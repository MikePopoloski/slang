add_custom_command(
  COMMAND ${Python_EXECUTABLE} ${SCRIPTS_DIR}/syntax_gen.py --dir
          ${CMAKE_CURRENT_BINARY_DIR} --python-bindings
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings.cpp
  DEPENDS ${SCRIPTS_DIR}/syntax_gen.py ${SCRIPTS_DIR}/syntax.txt
  COMMENT "Generating syntax bindings")

pybind11_add_module(
  pyslang
  MODULE
  source/compilation.cpp
  source/numeric.cpp
  source/pyslang.cpp
  source/syntax.cpp
  source/util.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/PySyntaxBindings.cpp)
target_link_libraries(pyslang PUBLIC slangcompiler)
target_include_directories(pyslang PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/source)
target_compile_definitions(pyslang PRIVATE VERSION_INFO=${PROJECT_VERSION})

install(
  TARGETS pyslang
  COMPONENT pylib
  DESTINATION .)

add_custom_target(
  pyslang-install-pylib
  ${CMAKE_COMMAND} -DCMAKE_INSTALL_COMPONENT=pylib -P
  "${PROJECT_BINARY_DIR}/cmake_install.cmake"
  DEPENDS pyslang)
