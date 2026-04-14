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

static_assert(std::is_trivially_destructible_v<ValueDriver>);

ValueDriver* ValueDriver::create(BumpAllocator& alloc, DriverKind kind, const ValuePath& path,
                                 const ast::Symbol& containingSymbol, bitmask<DriverFlags> flags,
                                 const SourceRange* overrideRange) {
    size_t size = sizeof(ValueDriver);
    if (overrideRange) {
        size += sizeof(SourceRange);
        flags |= DriverFlags::HasOverrideRange;
    }

    auto result = new (alloc.allocate(size, alignof(ValueDriver)))
        ValueDriver(kind, path, containingSymbol, flags);

    if (overrideRange)
        memcpy((void*)(result + 1), overrideRange, sizeof(SourceRange));

    return result;
}

ValueDriver* ValueDriver::create(BumpAllocator& alloc, EvalContext& evalContext,
                                 const ValueDriver& copyFrom, const ValueSymbol& newTarget) {
    auto newPath = copyFrom.path.retarget(alloc, evalContext, newTarget);
    auto result = create(alloc, copyFrom.kind, newPath, *copyFrom.containingSymbol, copyFrom.flags,
                         copyFrom.getOverrideRange());

    // The source is inferred during construction but the driver we're copying from
    // may have a different source that can't otherwise be inferred, so just copy
    // over whatever the constructor set for us.
    result->source = copyFrom.source;

    return result;
}

ValueDriver::ValueDriver(DriverKind kind, const ValuePath& path, const Symbol& containingSymbol,
                         bitmask<DriverFlags> flags) :
    path(path), containingSymbol(&containingSymbol), flags(flags), kind(kind) {

    SLANG_ASSERT(path.lsp && path.rootSymbol());

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
    return path.fullExpr->sourceRange;
}

const SourceRange* ValueDriver::getOverrideRange() const {
    if (flags.has(DriverFlags::HasOverrideRange))
        return reinterpret_cast<const SourceRange*>(this + 1);
    return nullptr;
}

} // namespace slang::analysis
