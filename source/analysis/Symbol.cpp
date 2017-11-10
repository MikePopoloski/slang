//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "diagnostics/Diagnostics.h"
#include "text/SourceManager.h"

#include "Binder.h"
#include "RootSymbol.h"

namespace {

using namespace slang;

TokenKind getIntegralKeywordKind(bool isFourState, bool isReg) {
    return !isFourState ? TokenKind::BitKeyword : isReg ? TokenKind::RegKeyword : TokenKind::LogicKeyword;
}

}

namespace slang {

VariableLifetime getLifetimeFromToken(Token token, VariableLifetime defaultIfUnset) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        case TokenKind::Unknown: return defaultIfUnset;
        default: THROW_UNREACHABLE;
    }
}

const Symbol* Symbol::findAncestor(SymbolKind searchKind) const {
    const Symbol* current = this;
    while (current->kind != searchKind) {
        if (current->kind == SymbolKind::Root)
            return nullptr;

        current = current->containingSymbol;
    }
    return current;
}

const ScopeSymbol& Symbol::containingScope() const {
    const Symbol* current = this;
    while (true) {
        current = current->containingSymbol;
        switch (current->kind) {
            case SymbolKind::Root:
            case SymbolKind::CompilationUnit:
            case SymbolKind::Package:
            case SymbolKind::ModuleInstance:
            case SymbolKind::InterfaceInstance:
            case SymbolKind::SequentialBlock:
            case SymbolKind::ProceduralBlock:
            case SymbolKind::IfGenerate:
            case SymbolKind::LoopGenerate:
            case SymbolKind::GenerateBlock:
            case SymbolKind::DynamicScope:
            case SymbolKind::Subroutine:
                return *static_cast<const ScopeSymbol*>(current);

            default: break;
        }
    }
}

const RootSymbol& Symbol::getRoot() const {
    const Symbol* symbol = findAncestor(SymbolKind::Root);
    ASSERT(symbol);
    return symbol->as<RootSymbol>();
}

Diagnostic& Symbol::addError(DiagCode code, SourceLocation location_) const {
    return getRoot().addError(code, location_);
}

const Symbol* ScopeSymbol::lookup(string_view searchName, SourceLocation lookupLocation,
                                  LookupKind lookupKind) const {
    ensureInit();

    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    // First, do a direct search within the current scope's name map.
    const SourceManager& sm = getRoot().sourceManager();
    auto it = memberMap.find(searchName);
    if (it != memberMap.end()) {
        // If this is a local or scoped lookup, check that we can access
        // the symbol (it must be declared before usage). Callables can be
        // referenced anywhere in the scope; location doesn't matter.
        bool locationGood = true;
        const Symbol* result = it->second;
        if (lookupKind == LookupKind::Local || lookupKind == LookupKind::Scoped)
            locationGood = sm.isBeforeInCompilationUnit(result->location, lookupLocation);

        if (locationGood) {
            // If this is a package import, unwrap it to return the imported symbol.
            // Direct lookups don't allow package imports, so ignore it in that case.
            if (result->kind == SymbolKind::ExplicitImport || result->kind == SymbolKind::ImplicitImport) {
                if (lookupKind != LookupKind::Direct)
                    return result->as<ExplicitImportSymbol>().importedSymbol();
            }
            else {
                return result;
            }
        }
    }

    // If we got here, we didn't find a viable symbol locally. Depending on the lookup
    // kind, try searching elsewhere.
    if (lookupKind == LookupKind::Direct)
        return nullptr;

    if (kind == SymbolKind::Root) {
        // For scoped lookups, if we reach the root without finding anything,
        // look for a package.
        if (lookupKind == LookupKind::Scoped)
            return getRoot().findPackage(searchName);
        return nullptr;
    }

    if (lookupKind != LookupKind::Definition) {
        // Check wildcard imports that lexically preceed the lookup location
        // to see if the symbol can be found in one of them.
        for (auto wildcard : wildcardImports) {
            if (sm.isBeforeInCompilationUnit(wildcard->location, lookupLocation)) {
                // TODO: if we find multiple, error and report all matching locations
                auto result = wildcard->resolve(searchName, lookupLocation);
                if (result) {
                    // TODO: this can cause other errors for this particular scope
                    //addMember(*result);
                    return result->importedSymbol();
                }
            }
        }
    }

    // Continue up the scope chain.
    return containingScope().lookup(searchName, lookupLocation, lookupKind);
}

SymbolList ScopeSymbol::members() const {
    ensureInit();
    return memberList;
}

ConstantValue ScopeSymbol::evaluateConstant(const ExpressionSyntax& expr) const {
    const auto& bound = Binder(*this).bindConstantExpression(expr);
    return bound.eval();
}

ConstantValue ScopeSymbol::evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType,
                                                      SourceLocation errorLocation) const {
    SourceLocation errLoc = errorLocation ? errorLocation : expr.getFirstToken().location();
    const auto& bound = Binder(*this).bindAssignmentLikeContext(expr, errLoc, targetType);
    return bound.eval();
}

void ScopeSymbol::MemberBuilder::add(const Symbol& symbol) {
    // TODO: check for duplicate names
    // TODO: packages and definition namespaces
    memberList.append(&symbol);
    if (!symbol.name.empty())
        memberMap.emplace(symbol.name, &symbol);

    if (symbol.kind == SymbolKind::WildcardImport)
        wildcardImports.append(&symbol.as<WildcardImportSymbol>());
}

void ScopeSymbol::MemberBuilder::add(const SyntaxNode& node, const ScopeSymbol& parent) {
    SmallVectorSized<const Symbol*, 8> symbols;
    parent.getRoot().factory.createSymbols(node, parent, symbols);
    for (auto symbol : symbols)
        add(*symbol);
}

void ScopeSymbol::setMember(const Symbol& member) {
    const Symbol* ptr = &member;
    setMembers(span<const Symbol* const>(&ptr, 1));
}

void ScopeSymbol::setMembers(span<const Symbol* const> members) {
    membersInitialized = true;

    MemberBuilder builder;
    for (auto member : members)
        builder.add(*member);

    copyMembers(builder);
}

void ScopeSymbol::doInit() const {
    membersInitialized = true;

    MemberBuilder builder;
    fillMembers(builder);
    copyMembers(builder);
}

void ScopeSymbol::copyMembers(MemberBuilder& builder) const {
    BumpAllocator& alloc = getRoot().allocator();
    memberMap = builder.memberMap.copy(alloc);
    memberList = builder.memberList.copy(alloc);
    wildcardImports = builder.wildcardImports.copy(alloc);
}

DynamicScopeSymbol::DynamicScopeSymbol(const Symbol& parent) : ScopeSymbol(SymbolKind::DynamicScope, parent) {}

void DynamicScopeSymbol::addSymbol(const Symbol& symbol) {
    members.push_back(&symbol);
    markDirty();
}

SymbolList DynamicScopeSymbol::createAndAddSymbols(const SyntaxNode& node) {
    SmallVectorSized<const Symbol*, 2> symbols;
    getRoot().factory.createSymbols(node, *this, symbols);
    for (auto symbol : symbols)
        addSymbol(*symbol);
    return symbols.copy(getRoot().factory.alloc);
}

void DynamicScopeSymbol::fillMembers(MemberBuilder& builder) const {
    for (auto member : members)
        builder.add(*member);
}

}
