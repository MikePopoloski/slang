pybind11_add_module(pyslang MODULE
    source/numeric.cpp
    source/pyslang.cpp
    source/syntax.cpp
    source/util.cpp
)
target_link_libraries(pyslang PUBLIC slangcompiler)
target_compile_definitions(pyslang PRIVATE VERSION_INFO=${PROJECT_VERSION})

install(TARGETS pyslang
        COMPONENT pylib
        DESTINATION .)

add_custom_target(pyslang-install-pylib
    ${CMAKE_COMMAND}
    -DCMAKE_INSTALL_COMPONENT=pylib
    -P "${PROJECT_BINARY_DIR}/cmake_install.cmake"
    DEPENDS pyslang)
