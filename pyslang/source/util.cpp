//------------------------------------------------------------------------------
// util.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include <fmt/format.h>
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>

#include "slang/text/SourceLocation.h"
#include "slang/util/BumpAllocator.h"

namespace py = pybind11;
using namespace slang;

void registerUtil(py::module_& m) {
    py::class_<BumpAllocator>(m, "BumpAllocator");

    py::class_<BufferID>(m, "BufferID")
        .def(py::init<>())
        .def_property_readonly("id", &BufferID::getId)
        .def_property_readonly_static("placeholder", &BufferID::getPlaceholder)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(hash(py::self))
        .def("__bool__", &BufferID::valid)
        .def("__repr__",
             [](const BufferID& self) { return fmt::format("BufferID({})", self.getId()); });

    py::class_<SourceLocation>(m, "SourceLocation")
        .def(py::init<>())
        .def(py::init<BufferID, size_t>())
        .def_property_readonly("buffer", &SourceLocation::buffer)
        .def_property_readonly("offset", &SourceLocation::offset)
        .def_readonly_static("NoLocation", &SourceLocation::NoLocation)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(hash(py::self))
        .def("__bool__", &SourceLocation::valid)
        .def("__repr__", [](const SourceLocation& self) {
            return fmt::format("SourceLocation({}, {})", self.buffer().getId(), self.offset());
        });

    py::class_<SourceRange>(m, "SourceRange")
        .def(py::init<>())
        .def(py::init<SourceLocation, SourceLocation>())
        .def_property_readonly("start", &SourceRange::start)
        .def_property_readonly("end", &SourceRange::end)
        .def(py::self == py::self)
        .def(py::self != py::self);
}
