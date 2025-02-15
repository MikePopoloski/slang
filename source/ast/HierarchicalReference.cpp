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
#include "slang/ast/symbols/InstanceSymbols.h"
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

const Symbol* HierarchicalReference::retargetIfacePort(const InstanceSymbol& base) const {
    if (!isViaIfacePort() || !target)
        return nullptr;

    auto port = base.body.findPort(path[0].symbol->name);
    if (!port)
        return nullptr;

    // TODO: think about modport restrictions
    auto [symbol, modport] = port->as<InterfacePortSymbol>().getConnection();
    for (size_t i = 1; i < path.size(); i++) {
        if (!symbol)
            return nullptr;

        if (symbol->kind == SymbolKind::Instance)
            symbol = &symbol->as<InstanceSymbol>().body;
        else if (!symbol->isScope())
            return nullptr;

        auto& elem = path[i];
        if (auto index = std::get_if<int32_t>(&elem.selector)) {
            // TODO: handle array indices
        }
        else {
            auto name = std::get<std::string_view>(elem.selector);
            symbol = symbol->as<Scope>().find(name);
        }
    }

    return symbol;
}

} // namespace slang::ast
