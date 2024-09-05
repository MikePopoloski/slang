//------------------------------------------------------------------------------
// HierarchicalReference.cpp
// Helper type for representing a hierarchical reference
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/HierarchicalReference.h"

#include "slang/ast/Symbol.h"

namespace slang::ast {

HierarchicalReference::Element::Element(const Symbol& symbol) :
    symbol(&symbol), selector(symbol.name) {
}

HierarchicalReference::Element::Element(const Symbol& symbol, int32_t index) :
    symbol(&symbol), selector(index) {
}

} // namespace slang::ast
