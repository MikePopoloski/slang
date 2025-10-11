//------------------------------------------------------------------------------
// ValueSymbol.cpp
// Base class for all value symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/ValueSymbol.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

ValueSymbol::ValueSymbol(SymbolKind kind, std::string_view name, SourceLocation location,
                         bitmask<DeclaredTypeFlags> flags) :
    Symbol(kind, name, location), declaredType(*this, flags) {
}

void ValueSymbol::setFromDeclarator(const DeclaratorSyntax& decl) {
    declaredType.setFromDeclarator(decl);
    setSyntax(decl);
}

bool ValueSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Net:
        case SymbolKind::EnumValue:
        case SymbolKind::Parameter:
        case SymbolKind::PrimitivePort:
        case SymbolKind::ModportPort:
        case SymbolKind::Specparam:
            return true;
        default:
            return VariableSymbol::isKind(kind);
    }
}

void ValueSymbol::addPortBackref(const PortSymbol& port) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    firstPortBackref = comp.emplace<PortBackref>(port, firstPortBackref);
}

bool ValueSymbol::isConnectedToRefPort() const {
    for (auto ref = firstPortBackref; ref; ref = ref->getNextBackreference()) {
        if (ref->port->direction == ArgumentDirection::Ref)
            return true;
    }
    return false;
}

} // namespace slang::ast
