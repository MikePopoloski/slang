//------------------------------------------------------------------------------
//! @file SvEnum.h
//! @brief Handles with SystemVerilog Enums
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "SvGeneric.h"

#include "slang/ast/types/AllTypes.h"

class SvEnum : public SvGeneric {
public:
    explicit SvEnum(const slang::ast::TypeAliasType& type) :
        SvGeneric(SvGeneric::Kind::Enum), type(type) {}

    void toCpp(HppFile& hppFile, std::string_view, const SvAliases&, bool noSystemC) const override;

private:
    const slang::ast::TypeAliasType& type;
};
