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

const LookupRefPoint LookupRefPoint::any;

Symbol::LazyConstant::LazyConstant(const Scope* scope) :
    Lazy(scope, &ConstantValue::Invalid) {}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(const ExpressionSyntax& source) {
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(source);
    return *this;
}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(ConstantValue result) {
    ConstantValue* p = storedScope->getCompilation().createConstant(std::move(result));
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(p);
    return *this;
}

const ConstantValue& Symbol::LazyConstant::evaluate(const Scope& scope,
                                                    const ExpressionSyntax& syntax) const {
    ConstantValue v = Binder(scope).bindConstantExpression(syntax).eval();
    return *scope.getCompilation().createConstant(std::move(v));
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
    return scope.getCompilation().getType(syntax, scope);
}

const Symbol::LazyDefinition::Value& Symbol::LazyDefinition::get() const {
    if (cache.index() == 0)
        return std::get<0>(cache);

    // TODO: module namespacing
    Source source = std::get<1>(cache);
    const DefinitionSymbol* definition = nullptr;
    ParamOverrideMap paramMap;

    Token typeName = source->type;
    LookupResult result;
    result.nameKind = LookupNameKind::Definition;
    scope->lookup(typeName.valueText(), result);

    const Symbol* foundSymbol = result.getFoundSymbol();
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
    return getScope()->getCompilation().addError(code, location_);
}

LookupRefPoint LookupRefPoint::before(const Symbol& symbol) {
    // TODO: look up the actual index of the symbol
    return LookupRefPoint(*symbol.getScope(), UINT32_MAX);
}

LookupRefPoint LookupRefPoint::after(const Symbol& symbol) {
    // TODO: look up the actual index of the symbol
    return LookupRefPoint(*symbol.getScope(), UINT32_MAX);
}

LookupRefPoint LookupRefPoint::startOfScope(const Scope& scope) {
    return LookupRefPoint(scope, 0);
}

LookupRefPoint LookupRefPoint::endOfScope(const Scope& scope) {
    return LookupRefPoint(scope, UINT32_MAX);
}

bool LookupRefPoint::operator<(const LookupRefPoint& other) const {
    if (scope == other.scope)
        return index < other.index;
    return scope;
}

void LookupResult::clear() {
    nameKind = LookupNameKind::Local;
    referencePoint = LookupRefPoint::any;
    resultKind = NotFound;
    resultWasImported = false;
    symbol = nullptr;
    imports.clear();
}

void LookupResult::setSymbol(const Symbol& found, bool wasImported) {
    symbol = &found;
    resultWasImported = wasImported;
    resultKind = Found;
}

void LookupResult::addPotentialImport(const Symbol& import) {
    if (!imports.empty())
        resultKind = AmbiguousImport;
    imports.append(&import);
}

Compilation& Scope::getCompilation() const {
    return thisSym->getRoot().compilation;
}

void Scope::lookup(string_view searchName, LookupResult& result) const {
    // First do a direct search and see if we find anything.
    auto nameEntry = lookupInternal(searchName);
    if (nameEntry) {
        // If this is a local or scoped lookup, check that we can access
        // the symbol (it must be declared before usage). Callables can be
        // referenced anywhere in the scope, so the location doesn't matter for them.
        bool locationGood = true;
        const Symbol* symbol = nameEntry->symbol;
        if (result.referencePointMatters())
            locationGood = LookupRefPoint(*this, nameEntry->index) < result.referencePoint;

        if (locationGood) {
            // We found the symbol we wanted. If it was an explicit package import, unwrap it first.
            if (symbol->kind == SymbolKind::ExplicitImport)
                // TODO: handle missing package import symbol
                result.setSymbol(*symbol->as<ExplicitImportSymbol>().importedSymbol(), true);
            else
                result.setSymbol(*symbol);
            return;
        }
    }

    // If we got here, we didn't find a viable symbol locally. Try looking in
    // any wildcard imports we may have.
    SmallVectorSized<std::tuple<ImportEntry*, const Symbol*>, 4> importResults;
    for (auto& importEntry : imports) {
        if (result.referencePoint < LookupRefPoint(*this, importEntry.index))
            break;

        // TODO: handle missing package
        auto symbol = importEntry.import->getPackage()->lookupDirect(searchName);
        if (symbol) {
            importResults.append(std::make_tuple(&importEntry, symbol));
            result.addPotentialImport(*symbol);
        }
    }

    if (!importResults.empty()) {
        if (importResults.size() == 1)
            result.setSymbol(*std::get<1>(importResults[0]), true);
        return;
    }

    if (thisSym->kind == SymbolKind::Root) {
        // For scoped lookups, if we reach the root without finding anything,
        // look for a package.
        // TODO: handle missing package
        if (result.nameKind == LookupNameKind::Scoped)
            result.setSymbol(*thisSym->getRoot().findPackage(searchName));
        return;
    }

    // Continue up the scope chain.
    return getParent()->lookup(searchName, result);
}

const Symbol* Scope::lookupDirect(string_view searchName) const {
    // Just do a simple lookup and return the result if we have one.
    // One wrinkle is that we should not include any imported symbols.
    auto result = lookupInternal(searchName);
    if (result && result->symbol->kind != SymbolKind::ExplicitImport)
        return result->symbol;
    return nullptr;
}

void Scope::setMembers(SymbolList list) {
    // TODO: don't require looking up the compilation for every scope like this
    nameMap = nullptr;
    memberList = getCompilation().makeCopy(list);
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

const SymbolMap::NameEntry* Scope::lookupInternal(string_view searchName) const {
    // Ensure our name map has been constructed.
    if (!nameMap)
        buildNameMap();

    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    return nameMap->find(searchName);
}

void Scope::buildNameMap() const {
    // TODO: make sure this doesn't become re-entrant when evaluating generate conditions
    nameMap = getCompilation().createSymbolMap();
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
    getRoot().compilation.createSymbols(node, *this, symbols);
    for (auto symbol : symbols)
        addSymbol(*symbol);
    return symbols.copy(getRoot().compilation);
}

LazySyntaxSymbol::LazySyntaxSymbol(const SyntaxNode& node, const Scope& parent, LazyDefinition* definition) :
    Symbol(SymbolKind::LazySyntax, parent),
    node(node),
    instanceDefinition(definition) {}

const Symbol* LazySyntaxSymbol::resolve() const {
    Compilation& compilation = getScope()->getCompilation();
    switch (node.kind) {
        case SyntaxKind::IfGenerate:
            return GenerateBlockSymbol::fromSyntax(compilation, node.as<IfGenerateSyntax>(), *getScope());
        case SyntaxKind::LoopGenerate:
            return &GenerateBlockArraySymbol::fromSyntax(compilation, node.as<LoopGenerateSyntax>(), *getScope());
        case SyntaxKind::HierarchicalInstance:
            ASSERT(instanceDefinition);
            return &InstanceSymbol::fromSyntax(compilation, node.as<HierarchicalInstanceSyntax>(),
                                               *instanceDefinition, *getScope());
        default:
            THROW_UNREACHABLE;
    }
}

Symbol& Symbol::clone(const Scope& newParent) const {
    Symbol* result;
    Compilation& compilation = getScope()->getCompilation();
#define CLONE(type) result = compilation.emplace<type>(*(const type*)this); break

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
