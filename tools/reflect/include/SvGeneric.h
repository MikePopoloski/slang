//------------------------------------------------------------------------------
//! @file SvGeneric.h
//! @brief Virtual parent class for SvEnum, SvLocalParam and SvStruct
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "CppEmitter.h"
#include <unordered_map>

using SvAliases = std::unordered_map<std::string_view, std::string_view>;

class SvGeneric {
public:
    enum class Kind { Struct, Enum, LocalParam, Union };
    explicit SvGeneric(const Kind kind) : kind(kind) {}

    virtual void toCpp(HppFile&, std::string_view, const SvAliases&, bool noSystemC) const = 0;

    [[nodiscard]] bool isStruct() const { return kind == Kind::Struct; }
    [[nodiscard]] bool isEnum() const { return kind == Kind::Enum; }
    [[nodiscard]] bool isLocalParam() const { return kind == Kind::LocalParam; }
    [[nodiscard]] bool isUnion() const { return kind == Kind::Union; }

    virtual ~SvGeneric() = default;

protected:
    Kind kind;

    [[nodiscard]] static std::string_view resolveAlias(const std::string_view& typeName,
                                                       const SvAliases& aliases) {
        if (const auto& alias = aliases.find(typeName); alias != aliases.end())
            return alias->second;
        return typeName;
    }

    [[nodiscard]] static bool isCppReserved(const std::string_view name) {
        return std::ranges::find(cppReservedKeywords, name) != cppReservedKeywords.end();
    }

    static constexpr std::array cppReservedKeywords = {"alignas",
                                                       "alignof",
                                                       "and",
                                                       "and_eq",
                                                       "asm",
                                                       "atomic_cancel",
                                                       "atomic_commit",
                                                       "atomic_noexcept",
                                                       "auto",
                                                       "bitand",
                                                       "bitor",
                                                       "bool",
                                                       "break",
                                                       "case",
                                                       "catch",
                                                       "char",
                                                       "char8_t",
                                                       "char16_t",
                                                       "char32_t",
                                                       "class",
                                                       "compl",
                                                       "concept",
                                                       "const",
                                                       "consteval",
                                                       "constexpr",
                                                       "constinit",
                                                       "const_cast",
                                                       "continue",
                                                       "co_await ",
                                                       "co_return ",
                                                       "co_yield",
                                                       "decltype",
                                                       "default",
                                                       "delete",
                                                       "do",
                                                       "double",
                                                       "dynamic_cast",
                                                       "else",
                                                       "enum",
                                                       "explicit",
                                                       "export",
                                                       "extern",
                                                       "false",
                                                       "float",
                                                       "for",
                                                       "friend",
                                                       "goto",
                                                       "if",
                                                       "inline",
                                                       "int",
                                                       "long",
                                                       "mutable",
                                                       "namespace",
                                                       "new",
                                                       "noexcept",
                                                       "not",
                                                       "not_eq",
                                                       "nullptr",
                                                       "operator",
                                                       "or",
                                                       "or_eq",
                                                       "private",
                                                       "protected",
                                                       "public",
                                                       "reflexpr",
                                                       "register",
                                                       "reinterpret_cast",
                                                       "requires",
                                                       "return",
                                                       "short",
                                                       "signed",
                                                       "sizeof",
                                                       "static",
                                                       "static_assert",
                                                       "static_cast",
                                                       "struct",
                                                       "switch",
                                                       "synchronized",
                                                       "template",
                                                       "this",
                                                       "thread_local",
                                                       "throw",
                                                       "true",
                                                       "try",
                                                       "typedef",
                                                       "typeid",
                                                       "typename",
                                                       "union",
                                                       "unsigned",
                                                       "using",
                                                       "virtual",
                                                       "void",
                                                       "volatile",
                                                       "wchar_t",
                                                       "while",
                                                       "xor",
                                                       "xor_eq"};
};
