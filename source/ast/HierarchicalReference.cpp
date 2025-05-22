//------------------------------------------------------------------------------
// HierarchicalReference.cpp
// Helper type for representing a hierarchical reference
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/HierarchicalReference.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/types/Type.h"

namespace slang::ast {

HierarchicalReference::Element::Element(const Symbol& symbol) :
    symbol(&symbol), selector(symbol.name) {
}

HierarchicalReference::Element::Element(const Symbol& symbol, int32_t index) :
    symbol(&symbol), selector(index) {
}

HierarchicalReference::Element::Element(const Symbol& symbol, std::pair<int32_t, int32_t> range) :
    symbol(&symbol), selector(range) {
}

HierarchicalReference HierarchicalReference::fromLookup(Compilation& compilation,
                                                        const LookupResult& result) {
    if (!result.flags.has(LookupResultFlags::IsHierarchical | LookupResultFlags::IfacePort))
        return {};

    HierarchicalReference ref;
    ref.target = result.found;
    ref.upwardCount = result.upwardCount;
    ref.path = result.path.copy(compilation);
    return ref;
}

bool HierarchicalReference::isViaIfacePort() const {
    return !path.empty() && path[0].symbol->kind == SymbolKind::InterfacePort;
}

bool HierarchicalReference::isUpward() const {
    return !isViaIfacePort() &&
           (upwardCount > 0 || (!path.empty() && path[0].symbol->kind == SymbolKind::Root));
}

const HierarchicalReference& HierarchicalReference::join(BumpAllocator& alloc,
                                                         const HierarchicalReference& other) const {
    HierarchicalReference result;
    result.target = other.target;
    result.expr = other.expr;
    result.upwardCount = upwardCount;

    auto otherPath = other.path;
    if (other.isViaIfacePort())
        otherPath = otherPath.subspan(1);

    SmallVector<Element> newPath;
    newPath.append_range(path);
    newPath.append_range(otherPath);
    result.path = newPath.copy(alloc);

    return *alloc.emplace<HierarchicalReference>(result);
}

} // namespace slang::ast
