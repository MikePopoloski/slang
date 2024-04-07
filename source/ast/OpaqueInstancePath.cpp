//------------------------------------------------------------------------------
// OpaqueInstancePath.cpp
// Helper type for representing an opaque path to an instance
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/OpaqueInstancePath.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"

namespace slang::ast {

OpaqueInstancePath::OpaqueInstancePath(const Symbol& symbol) {
    auto curr = &symbol;
    if (symbol.kind != SymbolKind::Instance) {
        while (curr->kind != SymbolKind::InstanceBody) {
            auto parent = curr->getHierarchicalParent();
            if (!parent)
                return;

            curr = &parent->asSymbol();
        }
    }
    buildPath(*curr);
}

void OpaqueInstancePath::buildPath(const Symbol& symbol) {
    auto scope = symbol.getHierarchicalParent();
    const Symbol* current;
    if (symbol.kind == SymbolKind::InstanceBody)
        current = symbol.as<InstanceBodySymbol>().parentInstance;
    else if (symbol.kind == SymbolKind::CheckerInstanceBody)
        current = symbol.as<CheckerInstanceBodySymbol>().parentInstance;
    else
        current = &symbol;

    SLANG_ASSERT(current);
    auto syntax = current->getSyntax();

    if (scope) {
        auto& parent = scope->asSymbol();
        if (parent.kind == SymbolKind::InstanceBody || parent.kind == SymbolKind::InstanceArray ||
            parent.kind == SymbolKind::CheckerInstance ||
            parent.kind == SymbolKind::GenerateBlock ||
            parent.kind == SymbolKind::GenerateBlockArray) {
            buildPath(parent);
        }
    }

    if (current->kind == SymbolKind::GenerateBlock) {
        if (scope && scope->asSymbol().kind == SymbolKind::GenerateBlockArray) {
            entries.push_back(current->as<GenerateBlockSymbol>().constructIndex);
            return;
        }
    }
    else if (current->kind == SymbolKind::Instance ||
             current->kind == SymbolKind::CheckerInstance) {
        auto& inst = current->as<InstanceSymbolBase>();
        if (!inst.arrayPath.empty()) {
            SmallVector<ConstantRange, 8> instanceDimVec;
            inst.getArrayDimensions(instanceDimVec);

            std::span<const ConstantRange> instanceDims = instanceDimVec;
            std::span<const int32_t> arrayPath = inst.arrayPath;
            SLANG_ASSERT(instanceDims.size() == arrayPath.size());

            for (size_t i = 0; i < instanceDims.size(); i++) {
                auto dim = instanceDims[i];
                entries.push_back((uint32_t)dim.translateIndex(arrayPath[i]));
            }
            return;
        }

        if (!syntax) {
            if (current->kind == SymbolKind::Instance)
                syntax = current->as<InstanceSymbol>().body.getSyntax();
            else
                syntax = current->as<CheckerInstanceSymbol>().body.getSyntax();
        }
    }
    else if (current->kind == SymbolKind::InstanceArray) {
        if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
            return;
    }

    SLANG_ASSERT(syntax);
    entries.push_back(*syntax);
}

} // namespace slang::ast
