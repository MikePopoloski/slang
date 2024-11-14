//------------------------------------------------------------------------------
//! @file SvLocalParam.h
//! @brief Handles with SystemVerilog local parameters
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#pragma once

#include "SvGeneric.h"
#include <fmt/format.h>

#include "slang/ast/symbols/ParameterSymbols.h"

class SvLocalParam final : public SvGeneric {
public:
    explicit SvLocalParam(const slang::ast::ParameterSymbol& parameter) :
        SvGeneric(Kind::LocalParam), parameter(parameter) {}

    void toCpp(HppFile& hppFile, std::string_view, const SvAliases&, bool) const override;

private:
    const slang::ast::ParameterSymbol& parameter;
};
