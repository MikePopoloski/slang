//------------------------------------------------------------------------------
// ValueDriver.cpp
// Tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/ValueDriver.h"

#include "slang/ast/symbols/BlockSymbols.h"

namespace slang::analysis {

using namespace ast;

ValueDriver::ValueDriver(DriverKind kind, const Expression& longestStaticPrefix,
                         const Symbol& containingSymbol, bitmask<AssignFlags> flags) :
    prefixExpression(&longestStaticPrefix), containingSymbol(&containingSymbol), flags(flags),
    kind(kind) {

    if (containingSymbol.kind == SymbolKind::ProceduralBlock) {
        source = static_cast<DriverSource>(
            containingSymbol.as<ProceduralBlockSymbol>().procedureKind);
    }
    else if (containingSymbol.kind == SymbolKind::Subroutine) {
        source = DriverSource::Subroutine;
    }
    else {
        source = DriverSource::Other;
    }
}

SourceRange ValueDriver::getSourceRange() const {
    if (procCallExpression)
        return procCallExpression->sourceRange;
    return prefixExpression->sourceRange;
}

} // namespace slang::analysis
