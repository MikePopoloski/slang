//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Scope.h"

#include "compilation/Compilation.h"
#include "symbols/Symbol.h"

namespace slang {

Scope::Scope(Compilation& compilation_, const Symbol* thisSym_) :
    compilation(compilation_), thisSym(thisSym_),
    nameMap(compilation.allocSymbolMap())
{
}

Scope::iterator& Scope::iterator::operator++() {
    current = current->nextInScope;
    return *this;
}

const Scope* Scope::getParent() const {
    return thisSym->getScope();
}

void Scope::addMember(const Symbol& symbol) {
    // For any symbols that expose a type, keep track of it in our
    // deferred data so that we can include enum values in our member list.
    const LazyType* lazyType = nullptr;
    switch (symbol.kind) {
        case SymbolKind::Variable:
        case SymbolKind::FormalArgument:
            lazyType = &symbol.as<VariableSymbol>().type;
            break;
        case SymbolKind::Subroutine:
            lazyType = &symbol.as<SubroutineSymbol>().returnType;
            break;
        case SymbolKind::Parameter:
            lazyType = &symbol.as<ParameterSymbol>().getLazyType();
            break;
        default:
            break;
    }

    if (lazyType) {
        auto syntax = lazyType->getSourceOrNull();
        if (syntax && syntax->kind == SyntaxKind::EnumType)
            getOrAddDeferredData().registerTransparentType(lastMember, *lazyType);
    }

    insertMember(&symbol, lastMember);
}

void Scope::addMembers(const SyntaxNode& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            compilation.addDefinition(syntax.as<ModuleDeclarationSyntax>(), *this);
            break;
        case SyntaxKind::PackageDeclaration:
            // Packages exist in their own namespace and are tracked in the Compilation
            compilation.addPackage(PackageSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>()));
            break;
        case SyntaxKind::PackageImportDeclaration:
            for (auto item : syntax.as<PackageImportDeclarationSyntax>().items) {
                if (item->item.kind == TokenKind::Star) {
                    auto import = compilation.emplace<WildcardImportSymbol>(
                        item->package.valueText(),
                        item->item.location());

                    addMember(*import);
                    compilation.trackImport(importDataIndex, *import);
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
            const auto& blockSyntax = syntax.as<ProceduralBlockSyntax>();
            auto kind = SemanticFacts::getProceduralBlockKind(blockSyntax.kind);
            addMember(*compilation.emplace<ProceduralBlockSymbol>(compilation,
                                                                  blockSyntax.keyword.location(),
                                                                  kind));
            break;
        }
        default:
            THROW_UNREACHABLE;
    }
}

const Symbol* Scope::find(string_view searchName) const {
    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    // Just do a simple lookup and return the result if we have one.
    ensureMembers();
    auto it = nameMap->find(searchName);
    if (it == nameMap->end())
        return nullptr;
    
    return it->second;
}

span<const WildcardImportSymbol* const> Scope::getImports() const {
    return compilation.queryImports(importDataIndex);
}

Scope::DeferredMemberData& Scope::getOrAddDeferredData() {
    return compilation.getOrAddDeferredData(deferredMemberIndex);
}

void Scope::insertMember(const Symbol* member, const Symbol* at) const {
    ASSERT(!member->parentScope);
    ASSERT(!member->nextInScope);

    if (!at) {
        member->indexInScope = Symbol::Index{ 1 };
        member->nextInScope = std::exchange(firstMember, member);
    }
    else {
        member->indexInScope = Symbol::Index{ (uint32_t)at->indexInScope + (at == lastMember) };
        member->nextInScope = std::exchange(at->nextInScope, member);
    }

    if (!member->nextInScope)
        lastMember = member;

    member->parentScope = this;
    if (!member->name.empty())
        nameMap->emplace(member->name, member);
}

void Scope::addDeferredMember(const SyntaxNode& member) {
    getOrAddDeferredData().addMember(member, lastMember);
}

void Scope::realizeDeferredMembers() const {
    ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto deferredData = compilation.getOrAddDeferredData(deferredMemberIndex);
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    for (const auto& pair : deferredData.getTransparentTypes()) {
        const Symbol* insertAt = pair.first;
        const Type* type = pair.second->get();

        if (type && type->kind == SymbolKind::EnumType) {
            for (auto value : type->as<EnumType>().values()) {
                auto wrapped = compilation.emplace<TransparentMemberSymbol>(*value);
                insertMember(wrapped, insertAt);
                insertAt = wrapped;
            }
        }
    }

    if (deferredData.hasStatement()) {
        auto syntax = deferredData.getStatement();
        ASSERT(syntax);

        // The const_cast should always be safe here; there's no way for statement
        // syntax to be added to our deferred members unless the original class
        // was non-const.
        static_cast<StatementBodiedScope*>(const_cast<Scope*>(this))->bindBody(*syntax);
    }
    else {
        for (auto[node, insertionPoint] : deferredData.getMembers()) {
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
}

}