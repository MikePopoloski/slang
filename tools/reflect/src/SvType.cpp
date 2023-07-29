// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "SvType.h"

#include <fmt/format.h>
#include <iostream>

#include "slang/ast/Definition.h"
#include "slang/ast/Scope.h"

using namespace slang::ast;

SvType::SvType(const Type& type) {
    size = type.bitstreamWidth();
    name = type.name;
    if (type.isScalar() || type.isArray())
        cppType = CppType::fromSize(size);
    else if (type.isEnum())
        cppType = CppType::ENUM;
    else if (type.isStruct() || type.isUnpackedStruct())
        cppType = CppType::STRUCT;
    else
        SLANG_UNREACHABLE;

    if (this->isEnum() || this->isStruct())
        _namespace = type.getParentScope()->asSymbol().name;
}

std::ostream& operator<<(std::ostream& os, const SvType& type) {
    return os << type.toString();
}

std::string SvType::toString() const {
    std::stringstream ss;
    if (cppType == CppType::SC_BV)
        ss << fmt::format(fmt::runtime(CppType::toString(cppType)), size);
    else if (this->isEnum() || this->isStruct())
        ss << fmt::format(fmt::runtime(CppType::toString(cppType)), name);
    else
        ss << CppType::toString(cppType);

    return ss.str();
}

namespace CppType {
std::string toString(const CppType::Type& cppType) {
    // clang-format off
    switch (cppType) {
        case BOOL: return "bool";
        case U32: return "uint32_t";
        case U64: return "uint64_t";
        case SC_BV: return "sc_bv<{}>";
        case STRUCT: return "{}";
        case ENUM: return "{}";
    }
    // clang-format on
    SLANG_UNREACHABLE;
}

CppType::Type fromSize(size_t size) {
    // clang-format off
        if (size == 1) return CppType::BOOL;
        else if (size <= 32) return CppType::U32;
        else if (size <= 64) return CppType::U64;
        else return CppType::SC_BV;
    // clang-format on
}
} // namespace CppType
