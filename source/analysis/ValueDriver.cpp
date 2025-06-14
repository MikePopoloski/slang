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
                         const Symbol& containingSymbol, bitmask<DriverFlags> flags) :
    prefixExpression(&longestStaticPrefix), containingSymbol(&containingSymbol), flags(flags),
    kind(kind) {

    switch (containingSymbol.kind) {
        case SymbolKind::ProceduralBlock:
            source = static_cast<DriverSource>(
                containingSymbol.as<ProceduralBlockSymbol>().procedureKind);
            break;
        case SymbolKind::Subroutine:
            source = DriverSource::Subroutine;
            break;
        default:
            source = DriverSource::Other;
            break;
    }
}

SourceRange ValueDriver::getSourceRange() const {
    if (procCallExpression)
        return procCallExpression->sourceRange;
    return prefixExpression->sourceRange;
}

} // namespace slang::analysis
