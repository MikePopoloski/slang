//------------------------------------------------------------------------------
//! @file ValueDriver.h
//! @brief Tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <vector>

namespace slang::ast {

class ValueDriver;
class ValueSymbol;

} // namespace slang::ast

namespace slang::analysis {

using DriverBitRange = std::pair<uint64_t, uint64_t>;
using DriverList = std::vector<std::pair<const ast::ValueDriver*, DriverBitRange>>;
using SymbolDriverListPair = std::pair<const ast::ValueSymbol*, DriverList>;

} // namespace slang::analysis
