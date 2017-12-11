//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "compilation/Compilation.h"
#include "diagnostics/Diagnostics.h"
#include "text/SourceManager.h"

#include "binding/Binder.h"

namespace slang {

const LookupRefPoint LookupRefPoint::any;

Symbol::LazyConstant::LazyConstant(ScopeOrSymbol parent) :
    Lazy(parent, &ConstantValue::Invalid) {}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(const ExpressionSyntax& source) {
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(source);
    return *this;
}

Symbol::LazyConstant& Symbol::LazyConstant::operator=(ConstantValue result) {
    ConstantValue* p = getScope().getCompilation().createConstant(std::move(result));
    Lazy<LazyConstant, ConstantValue, ExpressionSyntax>::operator=(p);
    return *this;
}

const ConstantValue& Symbol::LazyConstant::evaluate(const Scope& scope,
                                                    const ExpressionSyntax& syntax) const {
    ConstantValue v = Binder(scope).bindConstantExpression(syntax).eval();
    return *scope.getCompilation().createConstant(std::move(v));
}

Symbol::LazyStatement::LazyStatement(ScopeOrSymbol parent) :
    Lazy(parent, &InvalidStatement::Instance) {}

const Statement& Symbol::LazyStatement::evaluate(const Scope& scope,
                                                 const StatementSyntax& syntax) const {
    return Binder(scope).bindStatement(syntax);
}

Symbol::LazyStatementList::LazyStatementList(ScopeOrSymbol parent) :
    Lazy(parent, &StatementList::Empty) {}

const StatementList& Symbol::LazyStatementList::evaluate(const Scope& scope,
                                                         const SyntaxList<SyntaxNode>& list) const {
    return Binder(scope).bindStatementList(list);
}

Symbol::LazyInitializer::LazyInitializer(ScopeOrSymbol parent) :\
    Lazy(parent, nullptr) {}

const Expression& Symbol::LazyInitializer::evaluate(const Scope& scope,
                                                    const ExpressionSyntax& syntax) const {
    // TODO: bind assignment-like here
    return Binder(scope).bindConstantExpression(syntax);
}

Symbol::LazyType::LazyType(ScopeOrSymbol parent) :
    Lazy(parent, &ErrorTypeSymbol::Instance) {}

const TypeSymbol& Symbol::LazyType::evaluate(const Scope& scope,
                                             const DataTypeSyntax& syntax) const {
    return scope.getCompilation().getType(syntax, scope);
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

Scope::Scope(Compilation& compilation_, const Symbol* thisSym_) :
    compilation(compilation_), thisSym(thisSym_)
{
    nameMap = compilation.allocSymbolMap();
}

void Scope::addMember(const Symbol& symbol) {
    insertMember(&symbol, lastMember);
}

void Scope::addDeferredMember(const SyntaxNode& member) {
    compilation.addDeferredMembers(deferredMemberIndex, member, lastMember);
}

void Scope::addMembers(const SyntaxNode& syntax) {
    switch (syntax.kind) {
        // TODO: remove this?
        /*case SyntaxKind::CompilationUnit: {
            auto unit = compilation.emplace<CompilationUnitSymbol>(compilation);
            for (auto ms : syntax.as<CompilationUnitSyntax>().members)
                unit->addMembers(*ms);
            break;
        }*/
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            addMember(DefinitionSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>()));
            break;
        case SyntaxKind::PackageDeclaration:
            addMember(PackageSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>()));
            break;
        case SyntaxKind::PackageImportDeclaration:
            for (auto item : syntax.as<PackageImportDeclarationSyntax>().items) {
                if (item->item.kind == TokenKind::Star) {
                    addMember(*compilation.emplace<WildcardImportSymbol>(
                        item->package.valueText(),
                        item->item.location()));
                }
                else {
                    addMember(*compilation.emplace<ExplicitImportSymbol>(
                        item->package.valueText(),
                        item->item.valueText(),
                        item->item.location()));
                }
            }
            break;
        case SyntaxKind::HierarchyInstantiation:
            addDeferredMember(syntax);
            break;
        case SyntaxKind::ModportDeclaration:
            // TODO: modports
            break;
        case SyntaxKind::IfGenerate:
        case SyntaxKind::LoopGenerate:
            // TODO: add special name conflict checks for generate blocks
            addDeferredMember(syntax);
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            addMember(SubroutineSymbol::fromSyntax(compilation, syntax.as<FunctionDeclarationSyntax>()));
            break;
        case SyntaxKind::DataDeclaration: {
            SmallVectorSized<const VariableSymbol*, 4> variables;
            VariableSymbol::fromSyntax(compilation, syntax.as<DataDeclarationSyntax>(), variables);
            for (auto variable : variables)
                addMember(*variable);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            SmallVectorSized<ParameterSymbol*, 16> params;
            ParameterSymbol::fromSyntax(compilation,
                                        syntax.as<ParameterDeclarationStatementSyntax>().parameter,
                                        params);
            for (auto param : params)
                addMember(*param);
            break;
        }
        case SyntaxKind::ParameterDeclaration: {
            SmallVectorSized<ParameterSymbol*, 16> params;
            ParameterSymbol::fromSyntax(compilation,
                                        syntax.as<ParameterDeclarationSyntax>(),
                                        params);
            for (auto param : params)
                addMember(*param);
            break;
        }
        case SyntaxKind::GenerateBlock:
            for (auto member : syntax.as<GenerateBlockSyntax>().members)
                addMembers(*member);
            break;
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysLatchBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock: {
            auto kind = SemanticFacts::getProceduralBlockKind(syntax.as<ProceduralBlockSyntax>().kind);
            addMember(*compilation.emplace<ProceduralBlockSymbol>(compilation, kind));
            break;
        }
        default:
            THROW_UNREACHABLE;
    }
}

void Scope::lookup(string_view searchName, LookupResult& result) const {
    // First do a direct search and see if we find anything.
    ensureMembers();
    auto it = nameMap->find(searchName);
    if (it != nameMap->end()) {
        // If this is a local or scoped lookup, check that we can access
        // the symbol (it must be declared before usage). Callables can be
        // referenced anywhere in the scope, so the location doesn't matter for them.
        bool locationGood = true;
        const Symbol* symbol = it->second;
        if (result.referencePointMatters())
            locationGood = LookupRefPoint::before(*symbol) < result.referencePoint;

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
    //SmallVectorSized<std::tuple<ImportEntry*, const Symbol*>, 4> importResults;
    //for (auto& importEntry : imports) {
    //    if (result.referencePoint < LookupRefPoint(*this, importEntry.index))
    //        break;

    //    // TODO: handle missing package
    //    auto symbol = importEntry.import->getPackage()->lookupDirect(searchName);
    //    if (symbol) {
    //        importResults.append(std::make_tuple(&importEntry, symbol));
    //        result.addPotentialImport(*symbol);
    //    }
    //}

    //if (!importResults.empty()) {
    //    if (importResults.size() == 1)
    //        result.setSymbol(*std::get<1>(importResults[0]), true);
    //    return;
    //}

    if (thisSym->kind == SymbolKind::Root) {
        // For scoped lookups, if we reach the root without finding anything,
        // look for a package.
        // TODO: handle missing package
        if (result.nameKind == LookupNameKind::Scoped)
            result.setSymbol(*compilation.getPackage(searchName));
        return;
    }

    // Continue up the scope chain.
    return getParent()->lookup(searchName, result);
}

const Symbol* Scope::lookupDirect(string_view searchName) const {
    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    // Just do a simple lookup and return the result if we have one.
    // One wrinkle is that we should not include any imported symbols.
    ensureMembers();
    auto result = nameMap->find(searchName);
    if (result != nameMap->end() && result->second->kind != SymbolKind::ExplicitImport)
        return result->second;
    return nullptr;
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

void Scope::insertMember(const Symbol* member, const Symbol* at) const {
    ASSERT(!member->parentScope);
    ASSERT(!member->nextInScope);

    if (!at) {
        member->indexInScope = Symbol::Index { 1 };
        member->nextInScope = std::exchange(firstMember, member);
    }
    else {
        member->indexInScope = Symbol::Index { (uint32_t)at->indexInScope + 1 };
        member->nextInScope = std::exchange(at->nextInScope, member);
    }

    if (!member->nextInScope)
        lastMember = member;

    member->parentScope = this;
    if (!member->name.empty())
        nameMap->emplace(member->name, member);
}

void Scope::realizeDeferredMembers() const {
    ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto nodes = compilation.popDeferredMembers(deferredMemberIndex);
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    for (auto [node, insertionPoint] : nodes) {
        switch (node->kind) {
            case SyntaxKind::HierarchyInstantiation: {
                SmallVectorSized<const Symbol*, 8> symbols;
                InstanceSymbol::fromSyntax(compilation, node->as<HierarchyInstantiationSyntax>(),
                                           *this, symbols);

                const Symbol* last = insertionPoint;
                for (auto symbol : symbols) {
                    insertMember(symbol, last);
                    last = symbol;
                }
                break;
            }
            case SyntaxKind::IfGenerate: {
                auto block = GenerateBlockSymbol::fromSyntax(compilation,
                                                             node->as<IfGenerateSyntax>(), *this);
                if (block)
                    insertMember(block, insertionPoint);
                break;
            }
            case SyntaxKind::LoopGenerate: {
                const auto& block = GenerateBlockArraySymbol::fromSyntax(compilation,
                                                                         node->as<LoopGenerateSyntax>(),
                                                                         *this);
                insertMember(&block, insertionPoint);
                break;
            }
            default:
                THROW_UNREACHABLE;
        }
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
