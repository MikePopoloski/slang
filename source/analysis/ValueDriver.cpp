//------------------------------------------------------------------------------
// ValueDriver.cpp
// Tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/ValueDriver.h"

#include "slang/ast/LSPUtilities.h"
#include "slang/ast/symbols/BlockSymbols.h"

namespace slang::analysis {

using namespace ast;

static_assert(std::is_trivially_destructible_v<ValueDriver>);

ValueDriver* ValueDriver::create(BumpAllocator& alloc, DriverKind kind, const ast::Expression& lsp,
                                 const ast::Symbol& containingSymbol, bitmask<DriverFlags> flags,
                                 const SourceRange* overrideRange) {
    size_t size = sizeof(ValueDriver);
    if (overrideRange) {
        size += sizeof(SourceRange);
        flags |= DriverFlags::HasOverrideRange;
    }

    auto result = new (alloc.allocate(size, alignof(ValueDriver)))
        ValueDriver(kind, lsp, containingSymbol, flags);

    if (overrideRange)
        memcpy((void*)(result + 1), overrideRange, sizeof(SourceRange));

    return result;
}

ValueDriver* ValueDriver::create(BumpAllocator& alloc, const ValueDriver& copyFrom,
                                 const ValueSymbol& newTarget) {
    size_t size = sizeof(ValueDriver);
    const bool hasOverrideRange = copyFrom.flags.has(DriverFlags::HasOverrideRange);
    if (hasOverrideRange)
        size += sizeof(SourceRange);

    auto result = new (alloc.allocate(size, alignof(ValueDriver))) ValueDriver(copyFrom);
    if (hasOverrideRange)
        memcpy((void*)(result + 1), copyFrom.getOverrideRange(), sizeof(SourceRange));

    result->lsp = &LSPUtilities::retargetLSP(alloc, *result->lsp, newTarget);

    return result;
}

ValueDriver::ValueDriver(DriverKind kind, const Expression& lsp, const Symbol& containingSymbol,
                         bitmask<DriverFlags> flags) :
    lsp(&lsp), containingSymbol(&containingSymbol), flags(flags), kind(kind) {

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
    if (auto overrideRange = getOverrideRange())
        return *overrideRange;
    return lsp->sourceRange;
}

const SourceRange* ValueDriver::getOverrideRange() const {
    if (flags.has(DriverFlags::HasOverrideRange))
        return reinterpret_cast<const SourceRange*>(this + 1);
    return nullptr;
}

} // namespace slang::analysis
