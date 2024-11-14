//------------------------------------------------------------------------------
//! @file SvType.h
//! @brief C++ Type representation of a SystemVerilog type
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "slang/ast/types/Type.h"

namespace CppType {
enum Type { BOOL, U32, U64, SC_BV, STRUCT, ENUM, UNION };

std::string toString(const Type& cppType);
Type fromSize(size_t size);
} // namespace CppType

class SvType {
public:
    explicit SvType(const slang::ast::Type& type);
    explicit SvType(const slang::ast::Type& type, const std::string_view name) : SvType(type) {
        this->name = name;
    }

    [[nodiscard]] bool isStruct() const { return cppType == CppType::STRUCT; }
    [[nodiscard]] bool isEnum() const { return cppType == CppType::ENUM; }
    [[nodiscard]] bool isUnion() const { return cppType == CppType::UNION; }
    [[nodiscard]] bool isStructEnumOrUnion() const {
        return this->isStruct() || this->isEnum() || this->isUnion();
    }

    [[nodiscard]] std::string toString() const;
    friend std::ostream& operator<<(std::ostream& os, const SvType& type);

    CppType::Type cppType;
    size_t size;
    // It will only contain useful data if the cppType is either a struct or an enum
    std::string_view name;
    std::string_view _namespace;
};
