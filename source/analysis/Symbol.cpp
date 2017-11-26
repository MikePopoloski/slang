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

Symbol::LazyConstant::LazyConstant(const Scope* scope) :
    Lazy(scope, &ConstantValue::Invalid) {}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(const ExpressionSyntax& source) {
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(source);
    return *this;
}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(ConstantValue result) {
    ConstantValue* p = storedScope->getFactory().createConstant(std::move(result));
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(p);
    return *this;
}

const ConstantValue& Symbol::LazyConstant::evaluate(const Scope& scope,
                                                    const ExpressionSyntax& syntax) const {
    ConstantValue v = Binder(scope).bindConstantExpression(syntax).eval();
    return *scope.getFactory().createConstant(std::move(v));
}

Symbol::LazyStatement::LazyStatement(const Scope* scope) :
    Lazy(scope, &InvalidStatement::Instance) {}

const Statement& Symbol::LazyStatement::evaluate(const Scope& scope,
                                                 const StatementSyntax& syntax) const {
    return Binder(scope).bindStatement(syntax);
}

Symbol::LazyStatementList::LazyStatementList(const Scope* scope) :
    Lazy(scope, &StatementList::Empty) {}

const StatementList& Symbol::LazyStatementList::evaluate(const Scope& scope,
                                                         const SyntaxList<SyntaxNode>& list) const {
    return Binder(scope).bindStatementList(list);
}

Symbol::LazyInitializer::LazyInitializer(const Scope* scope) :\
    Lazy(scope, nullptr) {}

const Expression& Symbol::LazyInitializer::evaluate(const Scope& scope,
                                                    const ExpressionSyntax& syntax) const {
    // TODO: bind assignment-like here
    return Binder(scope).bindConstantExpression(syntax);
}

Symbol::LazyType::LazyType(const Scope* scope) :
    Lazy(scope, &ErrorTypeSymbol::Instance) {}

const TypeSymbol& Symbol::LazyType::evaluate(const Scope& scope,
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

        current = &current->getScope()->asSymbol();
    }
    return current;
}

const RootSymbol& Symbol::getRoot() const {
    const Symbol* symbol = findAncestor(SymbolKind::Root);
    ASSERT(symbol);
    return symbol->as<RootSymbol>();
}

Diagnostic& Symbol::addError(DiagCode code, SourceLocation location_) const {
    return getRoot().addError(code, location_);
}

SymbolFactory& Scope::getFactory() const {
    return thisSym->getRoot().factory;
}

const Symbol* Scope::lookup(string_view searchName, SourceLocation lookupLocation,
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

    if (thisSym->kind == SymbolKind::Root) {
        // For scoped lookups, if we reach the root without finding anything,
        // look for a package.
        if (lookupKind == LookupKind::Scoped)
            return thisSym->getRoot().findPackage(searchName);
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

void Scope::setMembers(SymbolList list) {
    // TODO: don't require looking up the factory for every scope like this
    nameMap = nullptr;
    memberList = getFactory().makeCopy(list);
}

ConstantValue Scope::evaluateConstant(const ExpressionSyntax& expr) const {
    const auto& bound = Binder(*this).bindConstantExpression(expr);
    return bound.eval();
}

ConstantValue Scope::evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType,
                                                      SourceLocation errorLocation) const {
    SourceLocation errLoc = errorLocation ? errorLocation : expr.getFirstToken().location();
    const auto& bound = Binder(*this).bindAssignmentLikeContext(expr, errLoc, targetType);
    return bound.eval();
}

void Scope::buildNameMap() const {
    // TODO: make sure this doesn't become re-entrant when evaluating generate conditions
    nameMap = getFactory().createSymbolMap();
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

DynamicScopeSymbol::DynamicScopeSymbol(const Scope& parent) :
    Symbol(SymbolKind::DynamicScope, parent),
    Scope(this)
{
}

void DynamicScopeSymbol::addSymbol(const Symbol& symbol) {
    members.push_back(&symbol);
    setMembers(members);
}

SymbolList DynamicScopeSymbol::createAndAddSymbols(const SyntaxNode& node) {
    SmallVectorSized<const Symbol*, 2> symbols;
    getRoot().factory.createSymbols(node, *this, symbols);
    for (auto symbol : symbols)
        addSymbol(*symbol);
    return symbols.copy(getRoot().factory);
}

LazySyntaxSymbol::LazySyntaxSymbol(const SyntaxNode& node, const Scope& parent, LazyDefinition* definition) :
    Symbol(SymbolKind::LazySyntax, parent),
    node(node),
    instanceDefinition(definition) {}

const Symbol* LazySyntaxSymbol::resolve() const {
    SymbolFactory& factory = getScope()->getFactory();
    switch (node.kind) {
        case SyntaxKind::IfGenerate:
            return GenerateBlockSymbol::fromSyntax(factory, node.as<IfGenerateSyntax>(), *getScope());
        case SyntaxKind::LoopGenerate:
            return &GenerateBlockArraySymbol::fromSyntax(factory, node.as<LoopGenerateSyntax>(), *getScope());
        case SyntaxKind::HierarchicalInstance:
            ASSERT(instanceDefinition);
            return &InstanceSymbol::fromSyntax(factory, node.as<HierarchicalInstanceSyntax>(),
                                               *instanceDefinition, *getScope());
        default:
            THROW_UNREACHABLE;
    }
}

Symbol& Symbol::clone(const Scope& newParent) const {
    Symbol* result;
    SymbolFactory& factory = getScope()->getFactory();
#define CLONE(type) result = factory.emplace<type>(*(const type*)this); break

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
