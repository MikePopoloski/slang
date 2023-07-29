//------------------------------------------------------------------------------
//! @file SvStruct.h
//! @brief Handles with SystemVerilog structs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "CppEmitter.h"
#include "SvGeneric.h"
#include "fmt/format.h"

class SvStruct : public SvGeneric {
public:
    explicit SvStruct(const slang::ast::TypeAliasType& type) :
        SvGeneric(SvGeneric::Kind::Struct), type(type) {}

    void toCpp(HppFile& hppFile, std::string_view _namespace, const SvAliases& aliases,
               bool noSystemC) const override;

private:
    const slang::ast::TypeAliasType& type;
};
