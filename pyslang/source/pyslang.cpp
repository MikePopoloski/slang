//------------------------------------------------------------------------------
// pyslang.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include <pybind11/pybind11.h>

#define STRINGIFY(x) #x
#define MACRO_STRINGIFY(x) STRINGIFY(x)

namespace py = pybind11;

void registerUtil(py::module_& m);
void registerSyntax(py::module_& m);

PYBIND11_MODULE(pyslang, m) {
    m.doc() = "Python bindings for slang, the SystemVerilog compiler library";

#ifdef VERSION_INFO
    m.attr("__version__") = MACRO_STRINGIFY(VERSION_INFO);
#else
    m.attr("__version__") = "dev";
#endif

    registerUtil(m);
    registerSyntax(m);
}
