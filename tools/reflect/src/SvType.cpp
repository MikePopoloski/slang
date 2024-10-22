// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvType.h"

#include <fmt/format.h>
#include <iostream>

#include "slang/ast/Scope.h"

using namespace slang::ast;

SvType::SvType(const Type& type) {
    size = type.getBitstreamWidth();
    name = type.name;
    if (type.isScalar() || type.isArray())
        cppType = CppType::fromSize(size);
    else if (type.isEnum())
        cppType = CppType::ENUM;
    else if (type.isStruct())
        cppType = CppType::STRUCT;
    else if (type.isUnion())
        cppType = CppType::UNION;
    else
        SLANG_UNREACHABLE;

    if (this->isStructEnumOrUnion())
        _namespace = type.getParentScope()->asSymbol().name;
}

std::ostream& operator<<(std::ostream& os, const SvType& type) {
    return os << type.toString();
}

std::string SvType::toString() const {
    std::stringstream ss;
    if (cppType == CppType::SC_BV)
        ss << format(fmt::runtime(CppType::toString(cppType)), size);
    else if (this->isStructEnumOrUnion())
        ss << format(fmt::runtime(CppType::toString(cppType)), name);
    else
        ss << CppType::toString(cppType);

    return ss.str();
}

namespace CppType {
std::string toString(const Type& cppType) {
    // clang-format off
    switch (cppType) {
        case BOOL: return "bool";
        case U32: return "uint32_t";
        case U64: return "uint64_t";
        case SC_BV: return "sc_bv<{}>";
        case STRUCT: return "{}";
        case ENUM: return "{}";
        case UNION: return "{}";
    }
    // clang-format on
    SLANG_UNREACHABLE;
}

Type fromSize(const size_t size) {
    // clang-format off
        if (size == 1) return BOOL;
        if (size <= 32) return U32;
        if (size <= 64) return U64;
        return SC_BV;
    // clang-format on
}
} // namespace CppType
