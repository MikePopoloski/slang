//------------------------------------------------------------------------------
// InstancePath.cpp
// Helper type for representing a hierarchical path to an instance
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/InstancePath.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"

namespace slang::ast {

InstancePath::InstancePath(const Symbol& symbol) {
    auto curr = &symbol;
    if (symbol.kind != SymbolKind::Instance) {
        while (curr->kind != SymbolKind::InstanceBody) {
            auto parent = curr->getParentScope();
            if (!parent)
                return;

            curr = &parent->asSymbol();
        }
    }
    buildPath(*curr);
}

void InstancePath::buildPath(const Symbol& symbol) {
    auto scope = symbol.getParentScope();
    auto current = &symbol;
    if (symbol.kind == SymbolKind::InstanceBody) {
        current = symbol.as<InstanceBodySymbol>().parentInstance;
        ASSERT(current);

        scope = current->getParentScope();
    }

    if (scope) {
        auto& parent = scope->asSymbol();
        if (parent.kind == SymbolKind::InstanceBody || parent.kind == SymbolKind::InstanceArray ||
            parent.kind == SymbolKind::GenerateBlock ||
            parent.kind == SymbolKind::GenerateBlockArray) {
            buildPath(parent);
        }
    }

    auto syntax = current->getSyntax();

    if (current->kind == SymbolKind::GenerateBlock) {
        if (scope && scope->asSymbol().kind == SymbolKind::GenerateBlockArray) {
            entries.push_back(current->as<GenerateBlockSymbol>().constructIndex);
            return;
        }
    }
    else if (current->kind == SymbolKind::Instance) {
        auto& inst = current->as<InstanceSymbol>();
        if (!inst.arrayPath.empty()) {
            SmallVector<ConstantRange, 8> instanceDimVec;
            inst.getArrayDimensions(instanceDimVec);

            span<const ConstantRange> instanceDims = instanceDimVec;
            span<const int32_t> arrayPath = inst.arrayPath;
            ASSERT(instanceDims.size() == arrayPath.size());

            for (size_t i = 0; i < instanceDims.size(); i++) {
                auto dim = instanceDims[i];
                entries.push_back((uint32_t)dim.translateIndex(arrayPath[i]));
            }
            return;
        }

        if (!syntax)
            syntax = inst.body.getSyntax();
    }
    else if (current->kind == SymbolKind::InstanceArray) {
        if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
            return;
    }

    ASSERT(syntax);
    entries.push_back(*syntax);
}

} // namespace slang::ast
