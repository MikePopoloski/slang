//------------------------------------------------------------------------------
// InstanceCacheKey.cpp
// Hash key for instance symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/InstanceCacheKey.h"

#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/types/Type.h"

namespace slang::ast {

bool InstanceCacheKey::isEligibleForCaching(const InstanceSymbol& symbol) {
    return !symbol.resolvedConfig && !symbol.body.hierarchyOverrideNode &&
           !symbol.body.flags.has(InstanceFlags::PreventsCaching);
}

InstanceCacheKey::InstanceCacheKey(const InstanceSymbol& symbol, bool& valid,
                                   SmallSet<const InstanceSymbol*, 2>& visitedInstances) :
    symbol(&symbol) {
    size_t h = 0;
    hash_combine(h, &symbol.getDefinition());

    for (auto param : symbol.body.getParameters()) {
        if (param->symbol.kind == SymbolKind::Parameter)
            hash_combine(h, param->symbol.as<ParameterSymbol>().getValue().hash());
        else
            hash_combine(h, param->symbol.as<TypeParameterSymbol>().targetType.getType().hash());
    }

    for (auto conn : symbol.getPortConnections()) {
        if (conn->port.kind == SymbolKind::InterfacePort) {
            auto [iface, modport] = conn->getIfaceConn();
            while (iface && iface->kind == SymbolKind::InstanceArray) {
                auto& arr = iface->as<InstanceArraySymbol>();
                if (arr.empty())
                    iface = nullptr;
                else
                    iface = arr.elements[0];
            }

            if (iface) {
                auto& ifaceInst = iface->as<InstanceSymbol>();
                if (!isEligibleForCaching(ifaceInst) ||
                    !visitedInstances.insert(&ifaceInst).second) {
                    valid = false;
                    return;
                }

                InstanceCacheKey ifaceKey(ifaceInst, valid, visitedInstances);
                if (!valid)
                    return;

                ifaceKeys.emplace_back(std::move(ifaceKey), modport);
                hash_combine(h, ifaceKeys.back().first.savedHash);

                if (modport)
                    hash_combine(h, modport->name);
            }
        }
    }

    savedHash = h;
}

bool InstanceCacheKey::operator==(const InstanceCacheKey& other) const {
    if (savedHash != other.savedHash ||
        &symbol->getDefinition() != &other.symbol->getDefinition() ||
        ifaceKeys.size() != other.ifaceKeys.size()) {
        return false;
    }

    auto lparams = symbol->body.getParameters();
    auto rparams = other.symbol->body.getParameters();
    SLANG_ASSERT(lparams.size() == rparams.size());

    for (size_t i = 0; i < lparams.size(); i++) {
        auto lp = lparams[i];
        auto rp = rparams[i];
        SLANG_ASSERT(lp->symbol.kind == rp->symbol.kind);

        if (lp->symbol.kind == SymbolKind::Parameter) {
            if (lp->symbol.as<ParameterSymbol>().getValue() !=
                rp->symbol.as<ParameterSymbol>().getValue()) {
                return false;
            }
        }
        else {
            auto& lt = lp->symbol.as<TypeParameterSymbol>().targetType.getType();
            auto& rt = rp->symbol.as<TypeParameterSymbol>().targetType.getType();
            if (!lt.isMatching(rt) && !lt.isIdenticalStructUnion(rt))
                return false;
        }
    }

    for (size_t i = 0; i < ifaceKeys.size(); i++) {
        auto& l = ifaceKeys[i];
        auto& r = other.ifaceKeys[i];
        if (l.first != r.first)
            return false;

        if (bool(l.second) != bool(r.second) || (l.second && l.second->name != r.second->name))
            return false;
    }

    return true;
}

} // namespace slang::ast
