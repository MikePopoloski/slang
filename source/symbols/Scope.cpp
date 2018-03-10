//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Scope.h"

#include "compilation/Compilation.h"
#include "symbols/Symbol.h"
#include "util/StackContainer.h"

namespace {

using namespace slang;

bool respectsLookupLocation(LookupNameKind kind) {
    switch (kind) {
        case LookupNameKind::Variable:
        case LookupNameKind::Type:
        case LookupNameKind::TypedefTarget:
        case LookupNameKind::BindTarget:
            return true;
        case LookupNameKind::Callable:
            return false;
    }
    THROW_UNREACHABLE;
}

}

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
    // For any symbols that expose a type to the surrounding scope, keep track of it in our
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
        case SymbolKind::TypeAlias:
            lazyType = &symbol.as<TypeAliasType>().targetType;
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
        case SyntaxKind::FinalBlock:
            addMember(ProceduralBlockSymbol::fromSyntax(compilation, syntax.as<ProceduralBlockSyntax>()));
            break;
        case SyntaxKind::EmptyMember:
            break;
        case SyntaxKind::TypedefDeclaration:
            addMember(TypeAliasType::fromSyntax(compilation, syntax.as<TypedefDeclarationSyntax>()));
            break;
        case SyntaxKind::ForwardTypedefDeclaration: {
            const auto& symbol = ForwardingTypedefSymbol::fromSyntax(compilation, syntax.as<ForwardTypedefDeclarationSyntax>());
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::ForwardInterfaceClassTypedefDeclaration: {
            const auto& symbol = ForwardingTypedefSymbol::fromSyntax(
                compilation,
                syntax.as<ForwardInterfaceClassTypedefDeclarationSyntax>()
            );
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::GenerateRegion:
            for (auto member : syntax.as<GenerateRegionSyntax>().members)
                addMembers(*member);
            break;
        default:
            THROW_UNREACHABLE;
    }
}

const Symbol* Scope::find(string_view name) const {
    // Just do a simple lookup and return the result if we have one.
    ensureElaborated();
    auto it = nameMap->find(name);
    if (it == nameMap->end())
        return nullptr;

    // Unwrap the symbol if it's a transparent member. Don't return imported
    // symbols; this function is for querying direct members only.
    const Symbol* symbol = it->second;
    switch (symbol->kind) {
        case SymbolKind::ExplicitImport: return nullptr;
        case SymbolKind::ForwardingTypedef: return nullptr;
        case SymbolKind::TransparentMember: return &symbol->as<TransparentMemberSymbol>().wrapped;
        default: return symbol;
    }
}

void Scope::lookupName(const NameSyntax& syntax, LookupLocation location, LookupNameKind nameKind,
                       LookupResult& result) const {
    Token nameToken;
    const SyntaxList<ElementSelectSyntax>* selectors = nullptr;
    switch (syntax.kind) {
        case SyntaxKind::IdentifierName:
            nameToken = syntax.as<IdentifierNameSyntax>().identifier;
            break;
        case SyntaxKind::IdentifierSelectName: {
            const auto& selectSyntax = syntax.as<IdentifierSelectNameSyntax>();
            nameToken = selectSyntax.identifier;
            selectors = &selectSyntax.selectors;
            break;
        }
        case SyntaxKind::ScopedName:
            // Handle qualified names completely separately.
            lookupQualified(syntax.as<ScopedNameSyntax>(), location, nameKind, result);
            return;
        default:
            THROW_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    if (nameToken.valueText().empty())
        return;

    // Perform the lookup.
    lookupUnqualified(nameToken.valueText(), location, nameKind, nameToken.range(), result);
    result.selectors = selectors;

    const Symbol* symbol = result.found;
    if (!symbol && !result.hasError()) {
        // Attempt to give a more helpful error if the symbol exists in scope but is declared after
        // the lookup location. Only do this if the symbol is of the kind we were expecting to find.
        bool usedBeforeDeclared = false;
        symbol = find(nameToken.valueText());
        if (symbol) {
            switch (nameKind) {
                case LookupNameKind::Variable:
                    usedBeforeDeclared = symbol->isValue();
                    break;
                case LookupNameKind::Type:
                case LookupNameKind::TypedefTarget:
                    usedBeforeDeclared = symbol->isType();
                    break;
                case LookupNameKind::Callable:
                case LookupNameKind::BindTarget:
                    break;
            }
        }

        if (!usedBeforeDeclared)
            result.diagnostics.add(DiagCode::UndeclaredIdentifier, nameToken.range()) << nameToken.valueText();
        else {
            auto& diag = result.diagnostics.add(DiagCode::UsedBeforeDeclared, nameToken.range());
            diag << nameToken.valueText();
            diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
        }
    }
}

const Symbol* Scope::lookupName(string_view name, LookupLocation location, LookupNameKind nameKind) const {
    LookupResult result;
    lookupName(compilation.parseName(name), location, nameKind, result);
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
    if (!member->name.empty()) {
        auto pair = nameMap->emplace(member->name, member);
        if (!pair.second) {
            // We have a name collision; first check if this is ok (forwarding typedefs share a name with
            // the actual typedef) and if not give the user a helpful error message.
            const Symbol* existing = pair.first->second;
            if (existing->kind == SymbolKind::TypeAlias && member->kind == SymbolKind::ForwardingTypedef) {
                // Just add this forwarding typedef to a deferred list so we can process them once we
                // know the kind of symbol the alias points to.
                existing->as<TypeAliasType>().addForwardDecl(member->as<ForwardingTypedefSymbol>());
            }
            else if (existing->kind == SymbolKind::ForwardingTypedef &&
                     member->kind == SymbolKind::ForwardingTypedef) {
                // Found another forwarding typedef; link it to the previous one.
                existing->as<ForwardingTypedefSymbol>().addForwardDecl(member->as<ForwardingTypedefSymbol>());
            }
            else if (existing->kind == SymbolKind::ForwardingTypedef && member->kind == SymbolKind::TypeAlias) {
                // We found the actual type for a previous forwarding declaration. Replace it in the name map.
                member->as<TypeAliasType>().addForwardDecl(existing->as<ForwardingTypedefSymbol>());
                pair.first->second = member;
            }
            else if (existing->kind == SymbolKind::ExplicitImport && member->kind == SymbolKind::ExplicitImport &&
                     existing->as<ExplicitImportSymbol>().packageName ==
                     member->as<ExplicitImportSymbol>().packageName) {
                // Duplicate explicit imports are specifically allowed, so just ignore the other one.
            }
            else {
                Diagnostic* diag;
                if (existing->isValue() && member->isValue()) {
                    const Type& memberType = member->as<ValueSymbol>().getType();
                    const Type& existingType = existing->as<ValueSymbol>().getType();
                    if (memberType.isMatching(existingType)) {
                        diag = &compilation.addError(DiagCode::Redefinition, member->location);
                        (*diag) << member->name;
                    }
                    else {
                        diag = &compilation.addError(DiagCode::RedefinitionDifferentType, member->location);
                        (*diag) << member->name << memberType << existingType;
                    }
                }
                else if (existing->kind != member->kind) {
                    diag = &compilation.addError(DiagCode::RedefinitionDifferentSymbolKind, member->location);
                    (*diag) << member->name;
                }
                else {
                    diag = &compilation.addError(DiagCode::Redefinition, member->location);
                    (*diag) << member->name;
                }
                diag->addNote(DiagCode::NotePreviousDefinition, existing->location);
            }
        }
    }
}

void Scope::addDeferredMember(const SyntaxNode& member) {
    getOrAddDeferredData().addMember(member, lastMember);
}

void Scope::elaborate() const {
    ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto deferredData = compilation.getOrAddDeferredData(deferredMemberIndex);
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    for (const auto& pair : deferredData.getTransparentTypes()) {
        const Symbol* insertAt = pair.first;
        const Type* type = pair.second->get();

        if (type && type->kind == SymbolKind::EnumType) {
            for (const auto& value : type->as<EnumType>().values()) {
                auto wrapped = compilation.emplace<TransparentMemberSymbol>(value);
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
        auto deferred = deferredData.getMembers();
        for (auto [node, insertionPoint] : make_range(deferred.rbegin(), deferred.rend())) {
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

    SmallSet<string_view, 4> observedForwardDecls;
    for (auto symbol : deferredData.getForwardingTypedefs()) {
        // Ignore duplicate entries.
        if (symbol->name.empty() || !observedForwardDecls.emplace(symbol->name).second)
            continue;

        // Try to do a lookup by name; if the program is well-formed we'll find the
        // corresponding full typedef. If we don't, issue an error.
        auto it = nameMap->find(symbol->name);
        ASSERT(it != nameMap->end());

        if (it->second->kind == SymbolKind::TypeAlias)
            it->second->as<TypeAliasType>().checkForwardDecls();
        else
            compilation.addError(DiagCode::UnresolvedForwardTypedef, symbol->location) << symbol->name;
    }
}

void Scope::lookupUnqualified(string_view name, LookupLocation location, LookupNameKind nameKind,
                              SourceRange sourceRange, LookupResult& result) const {
    ensureElaborated();
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
        if (respectsLookupLocation(nameKind)) {
            locationGood = LookupLocation::before(*symbol) < location;
            if (!locationGood && symbol->kind == SymbolKind::TypeAlias) {
                // A type alias can have forward definitions, so check those locations as well.
                // The forward decls form a linked list that are always ordered by location,
                // so we only need to check the first one.
                const ForwardingTypedefSymbol* forward = symbol->as<TypeAliasType>().getFirstForwardDecl();
                if (forward)
                    locationGood = LookupLocation::before(*forward) < location;
            }
        }

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
                case SymbolKind::ForwardingTypedef:
                    // If we find a forwarding typedef, the actual typedef was never defined. Just ignore it,
                    // we'll issue a better error later.
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
            auto& diag = result.diagnostics.add(DiagCode::AmbiguousWildcardImport, sourceRange) << name;
            for (const auto& pair : imports) {
                diag.addNote(DiagCode::NoteImportedFrom, pair.import->location);
                diag.addNote(DiagCode::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            auto& diag = result.diagnostics.add(DiagCode::ImportNameCollision, sourceRange) << name;
            diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
            diag.addNote(DiagCode::NoteImportedFrom, imports[0].import->location);
            diag.addNote(DiagCode::NoteDeclarationHere, imports[0].imported->location);
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

namespace {

using namespace slang;

// A downward lookup starts from a given scope and tries to match pieces of a name with subsequent members
// of scopes. If the entire path matches, the found member will be returned. Otherwise, the last name piece
// we looked up will be returned, along with whatever symbol was last found.
struct DownwardLookupResult {
    const Symbol* found;
    const NameSyntax* last;
};

DownwardLookupResult lookupDownward(span<const NameSyntax* const> nameParts, const Scope& scope) {
    const NameSyntax* const final = nameParts[nameParts.size() - 1];
    const Scope* current = &scope;
    const Symbol* found = nullptr;

    for (auto part : nameParts) {
        const Symbol* symbol;
        switch (part->kind) {
            case SyntaxKind::IdentifierName:
                symbol = current->find(part->as<IdentifierNameSyntax>().identifier.valueText());
                break;
            default:
                THROW_UNREACHABLE;
        }

        if (!symbol)
            return { found, part };

        found = symbol;
        if (part != final) {
            // This needs to be a scope, otherwise we can't do a lookup within it.
            if (!found->isScope())
                return { found, part };
            current = &found->as<Scope>();
        }
    }

    return { found, nullptr };
}

}

void Scope::lookupQualified(const ScopedNameSyntax& syntax, LookupLocation location,
                            LookupNameKind nameKind, LookupResult& result) const {
    // Split the name into easier to manage chunks. The parser will always produce a left-recursive
    // name tree, so that's all we'll bother to handle.
    int colonParts = 0;
    SmallVectorSized<const NameSyntax*, 8> nameParts;
    const ScopedNameSyntax* scoped = &syntax;
    while (true) {
        nameParts.append(&scoped->right);
        if (scoped->separator.kind == TokenKind::Dot)
            colonParts = 0;
        else
            colonParts++;

        if (scoped->left.kind == SyntaxKind::ScopedName)
            scoped = &scoped->left.as<ScopedNameSyntax>();
        else
            break;
    }

    Token nameToken;
    const NameSyntax* first = &scoped->left;
    switch (first->kind) {
        case SyntaxKind::IdentifierName:
            nameToken = first->as<IdentifierNameSyntax>().identifier;
            break;
        case SyntaxKind::IdentifierSelectName:
            //nameToken = first->as<IdentifierSelectNameSyntax>().identifier;
            //break;
        default:
            THROW_UNREACHABLE;
    }

    // Start by trying to find the first name segment using normal unqualified lookup.
    lookupUnqualified(nameToken.valueText(), location, nameKind, nameToken.range(), result);
    if (result.hasError())
        return;

    // If we are starting with a colon separator, always do a downwards name resolution. If the prefix name can
    // be resolved normally, we have a class scope, otherwise it's a package lookup. See [23.7.1]
    if (colonParts) {
        if (result.found) {
            // TODO: handle classes
            THROW_UNREACHABLE;
        }

        // Otherwise, it should be a package name.
        const PackageSymbol* package = compilation.getPackage(nameToken.valueText());
        if (!package) {
            result.diagnostics.add(DiagCode::UnknownClassOrPackage, nameToken.range()) << nameToken.valueText();
            return;
        }

        auto downward = lookupDownward(nameParts, *package);
        result.found = downward.found;
        return;
    }

    // Otherwise we have a dotted name; [23.7] lists the possible cases:
    // 1. The name resolves to a value symbol. The dotted name is a member select.
    // 2. The name resolves to a local scope. The dotted name is a hierarchical reference.
    // 3. The name resolves to an imported scope. The dotted name is a hierarchical reference,
    //    but with an added restriction that only a direct downward lookup from the package is allowed.
    // 4. The name is not found; it's considered a hierarchical reference and participates in
    //    upwards name resolution.
    if (result.found) {
        if (result.found->isValue()) {
            // The remainder of the names are member selects.
            result.memberSelects.appendRange(nameParts);
            return;
        }

        // TODO: handle scopes
        THROW_UNREACHABLE;
    }
}

}