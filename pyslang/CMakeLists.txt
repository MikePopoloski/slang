pybind11_add_module(pyslang
    source/numeric.cpp
    source/pyslang.cpp
    source/syntax.cpp
    source/util.cpp
)
target_link_libraries(pyslang PUBLIC slangcompiler)
