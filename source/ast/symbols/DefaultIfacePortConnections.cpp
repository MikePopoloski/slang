//------------------------------------------------------------------------------
// DefaultIfacePortConnections.cpp
// Contains support for synthesizing top-level interface port connections
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ParameterBuilder.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"

namespace slang::ast {

static Symbol* recurseDefaultIfaceInst(Compilation& comp, const InterfacePortSymbol& port,
                                       const InstanceSymbol*& firstInst,
                                       std::span<const ConstantRange>::iterator it,
                                       std::span<const ConstantRange>::iterator end) {
    if (it == end) {
        auto& def = *port.interfaceDef;
        ParameterBuilder paramBuilder(*def.getParentScope(), def.name, def.parameters);
        if (comp.hasFlag(CompilationFlags::AllowInvalidTop))
            paramBuilder.setSuppressErrors(true);
        // TODO: set parameters based on $static_assert constraints.
        auto& body = InstanceBodySymbol::fromDefinition(comp, def, port.location, paramBuilder,
                                                        InstanceFlags::None);

        auto& result = *comp.emplace<InstanceSymbol>(port.name, port.location, body, 0u);

        if (!firstInst)
            firstInst = &result;
        return &result;
    }

    ConstantRange range = *it++;
    if (range.width() > comp.getOptions().maxInstanceArray)
        return &InstanceArraySymbol::createEmpty(comp, port.name, port.location);

    SmallVector<const Symbol*> elements;
    for (uint32_t i = 0; i < range.width(); i++) {
        auto symbol = recurseDefaultIfaceInst(comp, port, firstInst, it, end);
        symbol->name = "";
        elements.push_back(symbol);
    }

    auto result = comp.emplace<InstanceArraySymbol>(comp, port.name, port.location,
                                                    elements.copy(comp), range);
    for (auto element : elements)
        result->addMember(*element);

    return result;
}

void InstanceSymbol::connectDefaultIfacePorts() const {
    auto parent = getParentScope();
    SLANG_ASSERT(parent);

    auto& comp = parent->getCompilation();
    ASTContext context(*parent, LookupLocation::max);

    SmallVector<const PortConnection*> conns;
    for (auto port : body.getPortList()) {
        if (port->kind == SymbolKind::InterfacePort) {
            auto& ifacePort = port->as<InterfacePortSymbol>();
            if (ifacePort.interfaceDef) {
                Symbol* inst;
                const ModportSymbol* modport = nullptr;
                if (auto dims = ifacePort.getDeclaredRange()) {
                    const InstanceSymbol* firstInst = nullptr;
                    inst = recurseDefaultIfaceInst(comp, ifacePort, firstInst, dims->begin(),
                                                   dims->end());

                    if (firstInst) {
                        auto portRange = SourceRange{port->location,
                                                     port->location + port->name.length()};
                        modport = ifacePort.getModport(context, *firstInst, portRange);
                    }
                }
                else {
                    inst = &InstanceArraySymbol::createEmpty(comp, port->name, port->location);
                }

                inst->setParent(*parent);
                conns.emplace_back(
                    comp.emplace<PortConnection>(ifacePort, std::pair{inst, modport}, nullptr));
                connectionMap->emplace(reinterpret_cast<uintptr_t>(port),
                                       reinterpret_cast<uintptr_t>(conns.back()));
            }
        }
    }
    connections = conns.copy(comp);
}

} // namespace slang::ast
