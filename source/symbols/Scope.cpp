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

const LookupLocation LookupLocation::max{ nullptr, UINT_MAX };
const LookupLocation LookupLocation::min{ nullptr, 0 };

LookupLocation LookupLocation::before(const Symbol& symbol) {
    return LookupLocation(symbol.getScope(), (uint32_t)symbol.getIndex());
}

LookupLocation LookupLocation::after(const Symbol& symbol) {
    return LookupLocation(symbol.getScope(), (uint32_t)symbol.getIndex() + 1);
}

bool LookupLocation::operator<(const LookupLocation& other) const {
    return index < other.index;
}

bool LookupResult::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    return !diagnostics.empty() || (!found && wasImported);
}

void LookupResult::clear() {
    found = nullptr;
    wasImported = false;
    diagnostics.clear();
}

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
        case SyntaxKind::EmptyMember:
            break;
        default:
            THROW_UNREACHABLE;
    }
}

const Symbol* Scope::find(string_view name) const {
    // Just do a simple lookup and return the result if we have one.
    ensureMembers();
    auto it = nameMap->find(name);
    if (it == nameMap->end())
        return nullptr;
    
    // Unwrap the symbol if it's a transparent member. Don't return imported
    // symbols; this function is for querying direct members only.
    const Symbol* symbol = it->second;
    switch (symbol->kind) {
        case SymbolKind::ExplicitImport: return nullptr;
        case SymbolKind::TransparentMember: return &symbol->as<TransparentMemberSymbol>().wrapped;
        default: return symbol;
    }
}

void Scope::lookupUnqualified(string_view name, LookupLocation location, LookupNameKind nameKind,
                              SourceRange sourceRange, LookupResult& result) const {
    ensureMembers();
    if (name.empty())
        return;

    // Try a simple name lookup to see if we find anything.
    const Symbol* symbol = nullptr;
    if (auto it = nameMap->find(name); it != nameMap->end()) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the scope,
        // so the location doesn't matter for them.
        symbol = it->second;
        bool locationGood = true;
        if (nameKind == LookupNameKind::Local)
            locationGood = LookupLocation::before(*symbol) < location;

        if (locationGood) {
            // Unwrap the symbol if it's hidden behind an import or hoisted enum member.
            switch (symbol->kind) {
                case SymbolKind::ExplicitImport:
                    result.found = symbol->as<ExplicitImportSymbol>().importedSymbol();
                    result.wasImported = true;
                    break;
                case SymbolKind::TransparentMember:
                    result.found = &symbol->as<TransparentMemberSymbol>().wrapped;
                    break;
                default:
                    result.found = symbol;
                    break;
            }
            return;
        }
    }

    // Look through any wildcard imports prior to the lookup point and see if their packages
    // contain the name we're looking for.
    struct Import {
        const Symbol* imported;
        const WildcardImportSymbol* import;
    };
    SmallVectorSized<Import, 8> imports;

    for (auto import : compilation.queryImports(importDataIndex)) {
        if (location < LookupLocation::after(*import))
            break;

        auto package = import->getPackage();
        if (!package)
            continue;

        const Symbol* imported = package->find(name);
        if (imported)
            imports.emplace(Import { imported, import });
    }

    if (!imports.empty()) {
        if (imports.size() > 1) {
            result.diagnostics.add(DiagCode::AmbiguousWildcardImport, sourceRange) << name;
            for (const auto& pair : imports) {
                result.diagnostics.add(DiagCode::NoteImportedFrom, pair.import->location);
                result.diagnostics.add(DiagCode::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            result.diagnostics.add(DiagCode::ImportNameCollision, sourceRange) << name;
            result.diagnostics.add(DiagCode::NoteDeclarationHere, symbol->location);
            result.diagnostics.add(DiagCode::NoteImportedFrom, imports[0].import->location);
            result.diagnostics.add(DiagCode::NoteDeclarationHere, imports[0].imported->location);
        }

        result.wasImported = true;
        result.found = imports[0].imported;
        return;
    }

    // Continue up the scope chain via our parent.
    auto nextScope = getParent();
    if (!nextScope)
        return;

    location = LookupLocation::after(asSymbol());
    return nextScope->lookupUnqualified(name, location, nameKind, sourceRange, result);
}

const Symbol* Scope::lookupUnqualified(string_view name, LookupLocation location, LookupNameKind nameKind) const {
    LookupResult result;
    lookupUnqualified(name, location, nameKind, SourceRange(), result);
    return result.found;
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
        for (auto [node, insertionPoint] : deferredData.getMembers()) {
            LookupLocation location = insertionPoint ? LookupLocation::after(*insertionPoint) : LookupLocation::min;
            switch (node->kind) {
                case SyntaxKind::HierarchyInstantiation: {
                    SmallVectorSized<const Symbol*, 8> symbols;
                    InstanceSymbol::fromSyntax(compilation, node->as<HierarchyInstantiationSyntax>(),
                                               location, *this, symbols);

                    const Symbol* last = insertionPoint;
                    for (auto symbol : symbols) {
                        insertMember(symbol, last);
                        last = symbol;
                    }
                    break;
                }
                case SyntaxKind::IfGenerate: {
                    auto block = GenerateBlockSymbol::fromSyntax(compilation,
                                                                 node->as<IfGenerateSyntax>(),
                                                                 location,
                                                                 *this);
                    if (block)
                        insertMember(block, insertionPoint);
                    break;
                }
                case SyntaxKind::LoopGenerate: {
                    const auto& block = GenerateBlockArraySymbol::fromSyntax(compilation,
                                                                             node->as<LoopGenerateSyntax>(),
                                                                             location,
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