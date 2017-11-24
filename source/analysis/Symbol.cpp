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

Symbol::LazyConstant::LazyConstant(const ScopeSymbol* scope) :
    Lazy(scope, &ConstantValue::Invalid) {}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(const ExpressionSyntax& source) {
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(source);
    return *this;
}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(ConstantValue result) {
    ConstantValue* p = storedScope->getRoot().constantAllocator.emplace(std::move(result));
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(p);
    return *this;
}

const ConstantValue& Symbol::LazyConstant::evaluate(const ScopeSymbol& scope,
                                                    const ExpressionSyntax& syntax) const {
    ConstantValue v = Binder(scope).bindConstantExpression(syntax).eval();
    return *scope.getRoot().constantAllocator.emplace(std::move(v));
}

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

const Symbol::LazyDefinition::Value& Symbol::LazyDefinition::get() const {
    if (cache.index() == 0)
        return std::get<0>(cache);

    // TODO: module namespacing
    Source source = std::get<1>(cache);
    const DefinitionSymbol* definition = nullptr;
    ParamOverrideMap paramMap;

    Token typeName = source->type;
    auto foundSymbol = scope->lookup(typeName.valueText(), typeName.location(), LookupKind::Definition);
    if (foundSymbol) {
        // TODO: check symbol kind?
        definition = &foundSymbol->as<DefinitionSymbol>();
        if (source->parameters)
            definition->createParamOverrides(*source->parameters, paramMap);
    }

    cache = std::make_tuple(definition, std::move(paramMap));
    return std::get<0>(cache);
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
    // Ensure our name map has been constructed.
    if (!nameMap)
        buildNameMap();

    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    // First, do a direct search within the current scope's name map.
    if (auto member = nameMap->find(searchName)) {
        // If this is a local or scoped lookup, check that we can access
        // the symbol (it must be declared before usage). Callables can be
        // referenced anywhere in the scope; location doesn't matter.
        bool locationGood = true;
        const Symbol* result = member->symbol;
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

    //if (lookupKind != LookupKind::Definition) {
    //    // Check wildcard imports that lexically preceed the lookup location
    //    // to see if the symbol can be found in one of them.
    //    for (auto wildcard : wildcardImports) {
    //        if (sm.isBeforeInCompilationUnit(wildcard->location, lookupLocation)) {
    //            // TODO: if we find multiple, error and report all matching locations
    //            auto result = wildcard->resolve(searchName, lookupLocation);
    //            if (result) {
    //                // TODO: this can cause other errors for this particular scope
    //                //addMember(*result);
    //                return result->importedSymbol();
    //            }
    //        }
    //    }
    //}

    // Continue up the scope chain.
    return getParent()->lookup(searchName, lookupLocation, lookupKind);
}

void ScopeSymbol::setMembers(SymbolList list) {
    nameMap = nullptr;
    memberList = getFactory().alloc.makeCopy(list);
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

void ScopeSymbol::buildNameMap() const {
    // TODO: make sure this doesn't become re-entrant when evaluating generate conditions
    nameMap = getFactory().symbolMapAllocator.emplace();
    for (uint32_t i = 0; i < memberList.size(); i++) {
        // If the symbol is lazy, replace it with the resolved symbol now.
        const Symbol* symbol = memberList[i];
        if (symbol->kind == SymbolKind::LazySyntax)
            memberList[i] = symbol = symbol->as<LazySyntaxSymbol>().resolve();

        // If the symbol has a name, we can look it up.
        if (!symbol->name.empty())
            nameMap->add(*symbol, i);
    }
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

LazySyntaxSymbol::LazySyntaxSymbol(const SyntaxNode& node, const ScopeSymbol& parent, LazyDefinition* definition) :
    Symbol(SymbolKind::LazySyntax, parent),
    node(node),
    instanceDefinition(definition) {}

const Symbol* LazySyntaxSymbol::resolve() const {
    SymbolFactory& factory = getFactory();
    switch (node.kind) {
        case SyntaxKind::IfGenerate:
            return GenerateBlockSymbol::fromSyntax(factory, node.as<IfGenerateSyntax>(), *getParent());
        case SyntaxKind::LoopGenerate:
            return &GenerateBlockArraySymbol::fromSyntax(factory, node.as<LoopGenerateSyntax>(), *getParent());
        case SyntaxKind::HierarchicalInstance:
            ASSERT(instanceDefinition);
            return &InstanceSymbol::fromSyntax(factory, node.as<HierarchicalInstanceSyntax>(),
                                               *instanceDefinition, *getParent());
        default:
            THROW_UNREACHABLE;
    }
}

Symbol& Symbol::clone(const ScopeSymbol& newParent) const {
    Symbol* result;
    SymbolFactory& factory = getFactory();
#define CLONE(type) result = factory.alloc.emplace<type>(*(const type*)this); break

    switch (kind) {
        case SymbolKind::CompilationUnit: CLONE(CompilationUnitSymbol);
        case SymbolKind::IntegralType: CLONE(IntegralTypeSymbol);
        case SymbolKind::RealType: CLONE(RealTypeSymbol);
        case SymbolKind::StringType: CLONE(TypeSymbol);
        case SymbolKind::CHandleType: CLONE(TypeSymbol);
        case SymbolKind::VoidType: CLONE(TypeSymbol);
        case SymbolKind::EventType: CLONE(TypeSymbol);
        case SymbolKind::TypeAlias: CLONE(TypeAliasSymbol);
        case SymbolKind::Parameter: CLONE(ParameterSymbol);
        case SymbolKind::Module: CLONE(DefinitionSymbol);
        case SymbolKind::Interface: CLONE(DefinitionSymbol);
        case SymbolKind::ModuleInstance: CLONE(ModuleInstanceSymbol);
        case SymbolKind::Package: CLONE(PackageSymbol);
        case SymbolKind::ExplicitImport: CLONE(ExplicitImportSymbol);
        case SymbolKind::ImplicitImport: CLONE(ImplicitImportSymbol);
        case SymbolKind::WildcardImport: CLONE(WildcardImportSymbol);
        case SymbolKind::Program: CLONE(DefinitionSymbol);
        case SymbolKind::GenerateBlock: CLONE(GenerateBlockSymbol);
        case SymbolKind::GenerateBlockArray: CLONE(GenerateBlockArraySymbol);
        case SymbolKind::ProceduralBlock: CLONE(ProceduralBlockSymbol);
        case SymbolKind::SequentialBlock: CLONE(SequentialBlockSymbol);
        case SymbolKind::Variable: CLONE(VariableSymbol);
        case SymbolKind::FormalArgument: CLONE(FormalArgumentSymbol);
        case SymbolKind::Subroutine: CLONE(SubroutineSymbol);
        default:
            THROW_UNREACHABLE;
    }
#undef CLONE

    result->parentScope = &newParent;
    return *result;
}

}
