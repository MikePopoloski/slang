//------------------------------------------------------------------------------
// pyslang.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/format.h>
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "slang/util/Enum.h"

#define STRINGIFY(x) #x
#define MACRO_STRINGIFY(x) STRINGIFY(x)

namespace py = pybind11;
using namespace pybind11::literals;
using namespace slang;

#define EXPOSE_ENUM(handle, name)                         \
    do {                                                  \
        py::enum_<name> e(handle, #name);                 \
        for (auto m : name##_traits::values) {            \
            e.value(std::string(toString(m)).c_str(), m); \
        }                                                 \
    } while (0)
