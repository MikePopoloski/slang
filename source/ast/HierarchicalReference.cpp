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

const Symbol* HierarchicalReference::retargetIfacePort(const InstanceSymbol& base) const {
    if (!isViaIfacePort() || !target)
        return nullptr;

    auto port = base.body.findPort(path[0].symbol->name);
    if (!port)
        return nullptr;

    auto [symbol, modport] = port->as<InterfacePortSymbol>().getConnection();
    for (size_t i = 1; i < path.size(); i++) {
        if (!symbol)
            return nullptr;

        if (symbol->kind == SymbolKind::Instance) {
            auto& body = symbol->as<InstanceSymbol>().body;
            symbol = &body;

            // See lookupDownward in Lookup.cpp for the logic here.
            if (modport) {
                symbol = body.find(modport->name);
                modport = nullptr;
                SLANG_ASSERT(symbol);
            }
        }
        else if (!symbol->isScope()) {
            return nullptr;
        }

        auto& elem = path[i];
        if (auto index = std::get_if<int32_t>(&elem.selector)) {
            if (symbol->kind == SymbolKind::InstanceArray) {
                auto& arr = symbol->as<InstanceArraySymbol>();
                if (*index < 0 || size_t(*index) >= arr.elements.size())
                    return nullptr;

                symbol = arr.elements[size_t(*index)];
            }
            else if (symbol->kind == SymbolKind::GenerateBlockArray) {
                auto& arr = symbol->as<GenerateBlockArraySymbol>();
                if (!arr.valid || *index < 0 || size_t(*index) >= arr.entries.size())
                    return nullptr;

                symbol = arr.entries[size_t(*index)];
            }
            else {
                return nullptr;
            }
        }
        else if (auto range = std::get_if<std::pair<int32_t, int32_t>>(&elem.selector)) {
            if (symbol->kind != SymbolKind::InstanceArray)
                return nullptr;

            auto& arr = symbol->as<InstanceArraySymbol>();
            if (range->first < 0 || size_t(range->second) >= arr.elements.size())
                return nullptr;

            if (size_t(range->first) >= arr.elements.size() ||
                size_t(range->second) >= arr.elements.size())
                return nullptr;

            auto elems = arr.elements.subspan(size_t(range->first),
                                              size_t(range->second - range->first) + 1);

            // Construct a placeholder array symbol that will hold this new sliced array.
            auto& comp = arr.getCompilation();
            symbol = comp.emplace<InstanceArraySymbol>(comp, ""sv, SourceLocation::NoLocation,
                                                       elems, ConstantRange{});
        }
        else {
            auto name = std::get<std::string_view>(elem.selector);
            auto next = symbol->as<Scope>().find(name);
            if (!next && symbol->kind == SymbolKind::Modport) {
                // See lookupDownward in Lookup.cpp for the logic here.
                next = symbol->getParentScope()->find(name);
                if (!next || SemanticFacts::isAllowedInModport(next->kind) ||
                    next->kind == SymbolKind::Modport) {
                    return nullptr;
                }
            }
            symbol = next;
        }
    }

    return symbol;
}

const HierarchicalReference& HierarchicalReference::join(Compilation& compilation,
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
    result.path = newPath.copy(compilation);

    return *compilation.emplace<HierarchicalReference>(result);
}

} // namespace slang::ast
