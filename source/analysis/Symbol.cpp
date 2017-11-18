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

namespace slang {

Symbol::LazyStatement::LazyStatement(const ScopeSymbol* scope) :
    Lazy(scope, &InvalidStatement::Instance) {}

const Statement& Symbol::LazyStatement::evaluate(const ScopeSymbol& scope,
                                                 const StatementSyntax& syntax) const {
    return Binder(scope).bindStatement(syntax);
}

Symbol::LazyStatementList::LazyStatementList(const ScopeSymbol* scope) :
    Lazy(scope, &StatementList::Empty) {}

const StatementList& Symbol::LazyStatementList::evaluate(const ScopeSymbol& scope,
                                                         const SyntaxList<SyntaxNode>& list) const {
    return Binder(scope).bindStatementList(list);
}

Symbol::LazyConstant::LazyConstant(const ScopeSymbol* scope) :
    Lazy(scope, &InvalidExpression::Instance) {}

const Expression& Symbol::LazyConstant::evaluate(const ScopeSymbol& scope,
                                                 const ExpressionSyntax& syntax) const {
    return Binder(scope).bindConstantExpression(syntax);
}

Symbol::LazyInitializer::LazyInitializer(const ScopeSymbol* scope) :\
    Lazy(scope, nullptr) {}

const Expression& Symbol::LazyInitializer::evaluate(const ScopeSymbol& scope,
                                                    const ExpressionSyntax& syntax) const {
    // TODO: bind assignment-like here
    return Binder(scope).bindConstantExpression(syntax);
}

Symbol::LazyType::LazyType(const ScopeSymbol* scope) :
    Lazy(scope, &ErrorTypeSymbol::Instance) {}

const TypeSymbol& Symbol::LazyType::evaluate(const ScopeSymbol& scope,
                                             const DataTypeSyntax& syntax) const {
    return scope.getFactory().getType(syntax, scope);
}

const Symbol* Symbol::findAncestor(SymbolKind searchKind) const {
    const Symbol* current = this;
    while (current->kind != searchKind) {
        if (current->kind == SymbolKind::Root)
            return nullptr;

        current = current->getParent();
    }
    return current;
}

const RootSymbol& Symbol::getRoot() const {
    const Symbol* symbol = findAncestor(SymbolKind::Root);
    ASSERT(symbol);
    return symbol->as<RootSymbol>();
}

SymbolFactory& Symbol::getFactory() const {
    return getRoot().factory;
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
        //if (lookupKind == LookupKind::Local || lookupKind == LookupKind::Scoped)
        //    locationGood = sm.isBeforeInCompilationUnit(result->location, lookupLocation);

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
    return getParent()->lookup(searchName, lookupLocation, lookupKind);
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

DynamicScopeSymbol::DynamicScopeSymbol(const ScopeSymbol& parent) : ScopeSymbol(SymbolKind::DynamicScope, parent) {}

void DynamicScopeSymbol::addSymbol(const Symbol& symbol) {
    members.push_back(&symbol);
    setMembers(members);
}

SymbolList DynamicScopeSymbol::createAndAddSymbols(const SyntaxNode& node) {
    SmallVectorSized<const Symbol*, 2> symbols;
    getRoot().factory.createSymbols(node, *this, symbols);
    for (auto symbol : symbols)
        addSymbol(*symbol);
    return symbols.copy(getRoot().factory.alloc);
}

}
