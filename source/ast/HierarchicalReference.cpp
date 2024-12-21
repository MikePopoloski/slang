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

namespace slang::ast {

HierarchicalReference::Element::Element(const Symbol& symbol) :
    symbol(&symbol), selector(symbol.name) {
}

HierarchicalReference::Element::Element(const Symbol& symbol, int32_t index) :
    symbol(&symbol), selector(index) {
}

HierarchicalReference HierarchicalReference::fromLookup(Compilation& compilation,
                                                        const LookupResult& result) {
    if (!result.flags.has(LookupResultFlags::IsHierarchical))
        return {};

    HierarchicalReference ref;
    ref.target = result.found;
    ref.upwardCount = result.upwardCount;
    ref.path = result.path.copy(compilation);
    return ref;
}

} // namespace slang::ast
