//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/Scope.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/Symbol.h"
#include "slang/util/StackContainer.h"

namespace {

using namespace slang;

// This is a placeholder symbol that we insert into a scope's member list where we need to
// later pull it out and replace it with a real member (that can't be known until full elaboration).
class DeferredMemberSymbol : public Symbol {
public:
    const SyntaxNode& node;

    explicit DeferredMemberSymbol(const SyntaxNode& node) :
        Symbol(SymbolKind::DeferredMember, "", SourceLocation()), node(node) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DeferredMember; }
};

} // namespace

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

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceLocation location) {
    return diagnostics.add(scope.asSymbol(), code, location);
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(scope.asSymbol(), code, sourceRange);
}

bool LookupResult::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    return !diagnostics.empty() || (!found && wasImported);
}

void LookupResult::clear() {
    found = nullptr;
    systemSubroutine = nullptr;
    wasImported = false;
    isHierarchical = false;
    diagnostics.clear();
}

Scope::Scope(Compilation& compilation_, const Symbol* thisSym_) :
    compilation(compilation_), thisSym(thisSym_), nameMap(compilation.allocSymbolMap()) {
}

Scope::iterator& Scope::iterator::operator++() {
    current = current->nextInScope;
    return *this;
}

const Scope* Scope::getParent() const {
    return thisSym->getScope();
}

Diagnostic& Scope::addDiag(DiagCode code, SourceLocation location) const {
    return compilation.addDiag(*thisSym, code, location);
}

Diagnostic& Scope::addDiag(DiagCode code, SourceRange sourceRange) const {
    return compilation.addDiag(*thisSym, code, sourceRange);
}

void Scope::addMember(const Symbol& symbol) {
    // For any symbols that expose a type to the surrounding scope, keep track of it in our
    // deferred data so that we can include enum values in our member list.
    const DeclaredType* declaredType = symbol.getDeclaredType();
    if (declaredType) {
        auto syntax = declaredType->getTypeSyntax();
        if (syntax && syntax->kind == SyntaxKind::EnumType)
            getOrAddDeferredData().registerTransparentType(lastMember, symbol);
    }

    insertMember(&symbol, lastMember);
}

void Scope::addMembers(const SyntaxNode& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration: {
            // Definitions exist in their own namespace and are tracked in the Compilation.
            // TODO: make this not going into the scope's name map
            auto& def =
                DefinitionSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>());
            addMember(def);
            compilation.addDefinition(def);
            break;
        }
        case SyntaxKind::PackageDeclaration: {
            // Packages exist in their own namespace and are tracked in the Compilation.
            // TODO: make this not going into the scope's name map
            auto& package =
                PackageSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>());
            addMember(package);
            compilation.addPackage(package);
            break;
        }
        case SyntaxKind::PackageImportDeclaration:
            for (auto item : syntax.as<PackageImportDeclarationSyntax>().items) {
                if (item->item.kind == TokenKind::Star) {
                    auto import = compilation.emplace<WildcardImportSymbol>(
                        item->package.valueText(), item->item.location());

                    import->setSyntax(*item);
                    addMember(*import);
                    compilation.trackImport(importDataIndex, *import);
                }
                else {
                    auto import = compilation.emplace<ExplicitImportSymbol>(
                        item->package.valueText(), item->item.valueText(), item->item.location());

                    import->setSyntax(*item);
                    addMember(*import);
                }
            }
            break;
        case SyntaxKind::HierarchyInstantiation:
        case SyntaxKind::AnsiPortList:
        case SyntaxKind::NonAnsiPortList:
        case SyntaxKind::IfGenerate:
        case SyntaxKind::LoopGenerate: {
            auto sym = compilation.emplace<DeferredMemberSymbol>(syntax);
            addMember(*sym);
            getOrAddDeferredData().addMember(sym);
            break;
        }
        case SyntaxKind::PortDeclaration:
            getOrAddDeferredData().addPortDeclaration(syntax.as<PortDeclarationSyntax>());
            break;
        case SyntaxKind::ModportDeclaration:
            for (auto item : syntax.as<ModportDeclarationSyntax>().items)
                addMember(ModportSymbol::fromSyntax(compilation, *item, *this));
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            addMember(SubroutineSymbol::fromSyntax(compilation,
                                                   syntax.as<FunctionDeclarationSyntax>(), *this));
            break;
        case SyntaxKind::DataDeclaration: {
            SmallVectorSized<const VariableSymbol*, 4> variables;
            VariableSymbol::fromSyntax(compilation, syntax.as<DataDeclarationSyntax>(), variables);
            for (auto variable : variables)
                addMember(*variable);
            break;
        }
        case SyntaxKind::NetDeclaration: {
            SmallVectorSized<const NetSymbol*, 4> nets;
            NetSymbol::fromSyntax(compilation, syntax.as<NetDeclarationSyntax>(), nets);
            for (auto net : nets)
                addMember(*net);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            SmallVectorSized<ParameterSymbol*, 16> params;
            ParameterSymbol::fromSyntax(compilation,
                                        *syntax.as<ParameterDeclarationStatementSyntax>().parameter,
                                        true, false, params);
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
            addMember(
                ProceduralBlockSymbol::fromSyntax(compilation, syntax.as<ProceduralBlockSyntax>()));
            break;
        case SyntaxKind::EmptyMember:
            break;
        case SyntaxKind::TypedefDeclaration:
            addMember(
                TypeAliasType::fromSyntax(compilation, syntax.as<TypedefDeclarationSyntax>()));
            break;
        case SyntaxKind::ForwardTypedefDeclaration: {
            const auto& symbol = ForwardingTypedefSymbol::fromSyntax(
                compilation, syntax.as<ForwardTypedefDeclarationSyntax>());
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::ForwardInterfaceClassTypedefDeclaration: {
            const auto& symbol = ForwardingTypedefSymbol::fromSyntax(
                compilation, syntax.as<ForwardInterfaceClassTypedefDeclarationSyntax>());
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::GenerateRegion:
            for (auto member : syntax.as<GenerateRegionSyntax>().members)
                addMembers(*member);
            break;
        case SyntaxKind::ContinuousAssign:
            for (auto expr : syntax.as<ContinuousAssignSyntax>().assignments)
                addMember(*compilation.emplace<ContinuousAssignSymbol>(*expr));
            break;
        default:
            // TODO: handle all cases
            addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
            break;
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
        case SymbolKind::ExplicitImport:
            return nullptr;
        case SymbolKind::ForwardingTypedef:
            return nullptr;
        case SymbolKind::TransparentMember:
            return &symbol->as<TransparentMemberSymbol>().wrapped;
        default:
            return symbol;
    }
}

void Scope::lookupName(const NameSyntax& syntax, LookupLocation location,
                       bitmask<LookupFlags> flags, LookupResult& result) const {
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
            lookupQualified(syntax.as<ScopedNameSyntax>(), location, flags, result);
            return;
        default:
            THROW_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    // If this is a system name, look up directly in the compilation.
    if (nameToken.identifierType() == IdentifierType::System) {
        result.found = nullptr;
        result.systemSubroutine = compilation.getSystemSubroutine(name);
        if (!result.systemSubroutine) {
            result.addDiag(*this, DiagCode::UndeclaredIdentifier, nameToken.range()) << name;
        }
        else if ((flags & LookupFlags::AllowSystemSubroutine) == 0) {
            result.addDiag(*this, DiagCode::UnexpectedSystemName, nameToken.range());
            result.systemSubroutine = nullptr;
        }
        return;
    }

    // Perform the lookup.
    lookupUnqualifiedImpl(name, location, nameToken.range(), flags, result);
    if (selectors)
        result.selectors.appendRange(*selectors);

    if (!result.found && !result.hasError())
        reportUndeclared(name, nameToken.range(), flags, result);
}

const Symbol* Scope::lookupUnqualifiedName(string_view name, LookupLocation location,
                                           SourceRange sourceRange,
                                           bitmask<LookupFlags> flags) const {
    LookupResult result;
    lookupUnqualifiedImpl(name, location, sourceRange, flags, result);
    if (result.hasError())
        getCompilation().addDiagnostics(result.getDiagnostics());

    return result.found;
}

const Symbol* Scope::lookupName(string_view name, LookupLocation location,
                                bitmask<LookupFlags> flags) const {
    LookupResult result;
    lookupName(compilation.parseName(name), location, flags, result);
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
        member->indexInScope = getInsertionIndex(*at);
        member->nextInScope = std::exchange(at->nextInScope, member);
    }

    member->parentScope = this;
    if (!member->nextInScope)
        lastMember = member;

    // Add to the name map if the symbol has a name, unless it's a port or definition symbol.
    // Per the spec, ports and definitions exist in their own namespaces.
    if (!member->name.empty() && member->kind != SymbolKind::Port &&
        member->kind != SymbolKind::Definition) {

        auto pair = nameMap->emplace(member->name, member);
        if (!pair.second) {
            // TODO: handle special generate block name conflict rules

            // We have a name collision; first check if this is ok (forwarding typedefs share a name
            // with the actual typedef) and if not give the user a helpful error message.
            const Symbol* existing = pair.first->second;
            if (existing->kind == SymbolKind::TypeAlias &&
                member->kind == SymbolKind::ForwardingTypedef) {
                // Just add this forwarding typedef to a deferred list so we can process them once
                // we know the kind of symbol the alias points to.
                existing->as<TypeAliasType>().addForwardDecl(member->as<ForwardingTypedefSymbol>());
            }
            else if (existing->kind == SymbolKind::ForwardingTypedef &&
                     member->kind == SymbolKind::ForwardingTypedef) {
                // Found another forwarding typedef; link it to the previous one.
                existing->as<ForwardingTypedefSymbol>().addForwardDecl(
                    member->as<ForwardingTypedefSymbol>());
            }
            else if (existing->kind == SymbolKind::ForwardingTypedef &&
                     member->kind == SymbolKind::TypeAlias) {
                // We found the actual type for a previous forwarding declaration. Replace it in the
                // name map.
                member->as<TypeAliasType>().addForwardDecl(existing->as<ForwardingTypedefSymbol>());
                pair.first->second = member;
            }
            else if (existing->kind == SymbolKind::ExplicitImport &&
                     member->kind == SymbolKind::ExplicitImport &&
                     existing->as<ExplicitImportSymbol>().packageName ==
                         member->as<ExplicitImportSymbol>().packageName) {
                // Duplicate explicit imports are specifically allowed, so just ignore the other
                // one.
            }
            else {
                Diagnostic* diag;
                if (existing->isValue() && member->isValue()) {
                    const Type& memberType = member->as<ValueSymbol>().getType();
                    const Type& existingType = existing->as<ValueSymbol>().getType();
                    if (memberType.isMatching(existingType)) {
                        diag = &addDiag(DiagCode::Redefinition, member->location);
                        (*diag) << member->name;
                    }
                    else {
                        diag = &addDiag(DiagCode::RedefinitionDifferentType, member->location);
                        (*diag) << member->name << memberType << existingType;
                    }
                }
                else if (existing->kind != member->kind) {
                    diag = &addDiag(DiagCode::RedefinitionDifferentSymbolKind, member->location);
                    (*diag) << member->name;
                }
                else {
                    diag = &addDiag(DiagCode::Redefinition, member->location);
                    (*diag) << member->name;
                }
                diag->addNote(DiagCode::NotePreviousDefinition, existing->location);
            }
        }
    }
}

Symbol::Index Scope::getInsertionIndex(const Symbol& at) const {
    return Symbol::Index{ (uint32_t)at.indexInScope + (&at == lastMember) };
}

void Scope::elaborate() const {
    ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto deferredData = compilation.getOrAddDeferredData(deferredMemberIndex);
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    for (const auto& pair : deferredData.getTransparentTypes()) {
        const Symbol* insertAt = pair.first;
        const Type& type = pair.second->getDeclaredType()->getType();

        if (type.kind == SymbolKind::EnumType) {
            for (const auto& value : type.as<EnumType>().values()) {
                auto wrapped = compilation.emplace<TransparentMemberSymbol>(value);
                insertMember(wrapped, insertAt);
                insertAt = wrapped;
            }
        }
    }

    if (deferredData.hasStatement()) {
        auto stmt = deferredData.getStatement();
        ASSERT(stmt);
        stmt->bindBody();
    }
    else {
        // Go through deferred members and elaborate them now. We skip generate blocks in
        // the initial pass because evaluating their conditions may depend on other members
        // that have yet to be elaborated. This implicitly implements the elaboration algorithm
        // described in [23.10.4.1].
        auto deferred = deferredData.getMembers();
        for (auto symbol : deferred) {
            auto& member = symbol->as<DeferredMemberSymbol>();
            switch (member.node.kind) {
                case SyntaxKind::HierarchyInstantiation: {
                    SmallVectorSized<const Symbol*, 8> instances;
                    LookupLocation location = LookupLocation::before(*symbol);
                    InstanceSymbol::fromSyntax(compilation,
                                               member.node.as<HierarchyInstantiationSyntax>(),
                                               location, *this, instances);

                    const Symbol* last = symbol;
                    for (auto instance : instances) {
                        insertMember(instance, last);
                        last = instance;
                    }
                    break;
                }
                case SyntaxKind::AnsiPortList:
                case SyntaxKind::NonAnsiPortList: {
                    SmallVectorSized<Symbol*, 8> ports;
                    PortSymbol::fromSyntax(member.node.as<PortListSyntax>(), *this, ports,
                                           deferredData.getPortDeclarations());

                    // Only a few kinds of symbols can have port maps; grab that port map
                    // now so we can add each port to it for future lookup.
                    // The const_cast here is ugly but valid.
                    SymbolMap* portMap;
                    const Symbol& sym = asSymbol();
                    if (sym.kind == SymbolKind::Definition)
                        portMap = const_cast<SymbolMap*>(&sym.as<DefinitionSymbol>().getPortMap());
                    else if (InstanceSymbol::isKind(sym.kind))
                        portMap = const_cast<SymbolMap*>(&sym.as<InstanceSymbol>().getPortMap());
                    else
                        THROW_UNREACHABLE;

                    const Symbol* last = symbol;
                    for (auto port : ports) {
                        portMap->emplace(port->name, port);
                        insertMember(port, last);
                        last = port;

                        if (port->kind == SymbolKind::Port) {
                            auto& valuePort = port->as<PortSymbol>();
                            if (valuePort.internalSymbol && !valuePort.internalSymbol->getScope()) {
                                insertMember(valuePort.internalSymbol, last);
                                last = valuePort.internalSymbol;
                            }
                        }
                    }

                    // If we have port connections, tie them to the ports now.
                    if (auto connections = deferredData.getPortConnections())
                        PortSymbol::makeConnections(*this, ports, *connections);

                    break;
                }
                default:
                    break;
            }
        }

        // Now that all instances have been inserted, go back through and elaborate generate
        // blocks. The spec requires that we give each generate construct an index, starting from
        // one. This index is used to generate external names for unnamed generate blocks.
        uint32_t constructIndex = 1;
        for (auto symbol : deferred) {
            auto& member = symbol->as<DeferredMemberSymbol>();
            LookupLocation location = LookupLocation::before(*symbol);

            switch (member.node.kind) {
                case SyntaxKind::IfGenerate: {
                    SmallVectorSized<GenerateBlockSymbol*, 8> blocks;
                    GenerateBlockSymbol::fromSyntax(compilation, member.node.as<IfGenerateSyntax>(),
                                                    location, *this, constructIndex, true, blocks);

                    const Symbol* last = symbol;
                    for (auto block : blocks) {
                        insertMember(block, last);
                        last = block;
                    }
                    break;
                }
                case SyntaxKind::LoopGenerate:
                    insertMember(&GenerateBlockArraySymbol::fromSyntax(
                                     compilation, member.node.as<LoopGenerateSyntax>(),
                                     getInsertionIndex(*symbol), location, *this, constructIndex),
                                 symbol);
                    break;
                default:
                    break;
            }

            constructIndex++;
        }

        // Finally unlink any deferred members we had; we no longer need them.
        if (!deferred.empty()) {
            const Symbol* symbol = firstMember;
            const Symbol* prev = nullptr;

            while (symbol) {
                if (symbol->kind == SymbolKind::DeferredMember) {
                    if (prev)
                        prev->nextInScope = symbol->nextInScope;
                    else
                        firstMember = symbol->nextInScope;

                    if (lastMember == symbol)
                        lastMember = symbol->nextInScope;
                }
                else {
                    prev = symbol;
                }
                symbol = symbol->nextInScope;
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
            addDiag(DiagCode::UnresolvedForwardTypedef, symbol->location) << symbol->name;
    }
}

void Scope::lookupUnqualifiedImpl(string_view name, LookupLocation location,
                                  SourceRange sourceRange, bitmask<LookupFlags> flags,
                                  LookupResult& result) const {
    ensureElaborated();
    if (name.empty())
        return;

    // Try a simple name lookup to see if we find anything.
    const Symbol* symbol = nullptr;
    if (auto it = nameMap->find(name); it != nameMap->end()) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the
        // scope, so the location doesn't matter for them.
        symbol = it->second;
        bool locationGood = true;
        if ((flags & LookupFlags::AllowDeclaredAfter) == 0) {
            locationGood = LookupLocation::before(*symbol) < location;
            if (!locationGood && symbol->kind == SymbolKind::TypeAlias) {
                // A type alias can have forward definitions, so check those locations as well.
                // The forward decls form a linked list that are always ordered by location,
                // so we only need to check the first one.
                const ForwardingTypedefSymbol* forward =
                    symbol->as<TypeAliasType>().getFirstForwardDecl();
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
                    // If we find a forwarding typedef, the actual typedef was never defined.
                    // Just ignore it, we'll issue a better error later.
                    break;
                default:
                    result.found = symbol;
                    break;
            }

            // We have a fully resolved and valid symbol. Before we return back to the caller,
            // make sure that the symbol we're returning isn't in the process of having its type
            // evaluated. This can only happen with a mutually recursive definition of something
            // like a parameter and a function, so detect and report the error here to avoid a
            // stack overflow.
            if (result.found) {
                const DeclaredType* declaredType = result.found->getDeclaredType();
                if (declaredType && declaredType->isEvaluating()) {
                    auto& diag = result.addDiag(*this, DiagCode::RecursiveDefinition, sourceRange)
                                 << name;
                    diag.addNote(DiagCode::NoteDeclarationHere, result.found->location);
                    result.found = nullptr;
                }
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
            imports.emplace(Import{ imported, import });
    }

    if (!imports.empty()) {
        if (imports.size() > 1) {
            auto& diag = result.addDiag(*this, DiagCode::AmbiguousWildcardImport, sourceRange)
                         << name;
            for (const auto& pair : imports) {
                diag.addNote(DiagCode::NoteImportedFrom, pair.import->location);
                diag.addNote(DiagCode::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            auto& diag = result.addDiag(*this, DiagCode::ImportNameCollision, sourceRange) << name;
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
    return nextScope->lookupUnqualifiedImpl(name, location, sourceRange, flags, result);
}

namespace {

using namespace slang;

// A downward lookup starts from a given scope and tries to match pieces of a name with
// subsequent members of scopes. If the entire path matches, the found member will be returned.
// Otherwise, the last name piece we looked up will be returned, along with whatever symbol was
// last found.
struct DownwardLookupResult {
    const Symbol* found;
    const NameSyntax* last;
};

struct NamePlusLoc {
    const NameSyntax* name;
    SourceLocation dotLocation;
};

DownwardLookupResult lookupDownward(span<const NamePlusLoc> nameParts, const Scope& scope) {
    const NameSyntax* const final = nameParts[nameParts.size() - 1].name;
    const Scope* current = &scope;
    const Symbol* found = nullptr;

    for (auto part : nameParts) {
        const Symbol* symbol;
        switch (part.name->kind) {
            case SyntaxKind::IdentifierName:
                symbol =
                    current->find(part.name->as<IdentifierNameSyntax>().identifier.valueText());
                break;
            default:
                THROW_UNREACHABLE;
        }

        if (!symbol)
            return { found, part.name };

        found = symbol;
        if (part.name != final) {
            // This needs to be a scope, otherwise we can't do a lookup within it.
            if (!found->isScope())
                return { found, part.name };
            current = &found->as<Scope>();
        }
    }

    return { found, nullptr };
}

} // namespace

void Scope::lookupQualified(const ScopedNameSyntax& syntax, LookupLocation location,
                            bitmask<LookupFlags> flags, LookupResult& result) const {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    int colonParts = 0;
    SmallVectorSized<NamePlusLoc, 8> nameParts;
    const ScopedNameSyntax* scoped = &syntax;
    while (true) {
        nameParts.append({ scoped->right, scoped->separator.location() });
        if (scoped->separator.kind == TokenKind::Dot)
            colonParts = 0;
        else
            colonParts++;

        if (scoped->left->kind == SyntaxKind::ScopedName)
            scoped = &scoped->left->as<ScopedNameSyntax>();
        else
            break;
    }

    Token nameToken;
    const SyntaxList<ElementSelectSyntax>* selectors = nullptr;
    const NameSyntax* first = scoped->left;
    switch (first->kind) {
        case SyntaxKind::IdentifierName:
            nameToken = first->as<IdentifierNameSyntax>().identifier;
            break;
        case SyntaxKind::IdentifierSelectName: {
            const auto& idSelect = first->as<IdentifierSelectNameSyntax>();
            nameToken = idSelect.identifier;
            selectors = &idSelect.selectors;
            break;
        }
        default:
            THROW_UNREACHABLE;
    }

    if (nameToken.valueText().empty())
        return;

    // Start by trying to find the first name segment using normal unqualified lookup.
    lookupUnqualifiedImpl(nameToken.valueText(), location, nameToken.range(), flags, result);
    if (result.hasError())
        return;

    // If we are starting with a colon separator, always do a downwards name resolution. If the
    // prefix name can be resolved normally, we have a class scope, otherwise it's a package
    // lookup. See [23.7.1]
    if (colonParts) {
        if (result.found && result.found->kind != SymbolKind::Package) {
            // TODO: handle classes
            THROW_UNREACHABLE;
        }

        // Otherwise, it should be a package name.
        const PackageSymbol* package = result.found ? &result.found->as<PackageSymbol>()
                                                    : compilation.getPackage(nameToken.valueText());

        if (!package) {
            result.addDiag(*this, DiagCode::UnknownClassOrPackage, nameToken.range())
                << nameToken.valueText();
            return;
        }

        // TODO: error if selectors

        auto downward = lookupDownward(nameParts, *package);
        result.found = downward.found;
        return;
    }

    // Otherwise we have a dotted name; [23.7] lists the possible cases:
    // 1. The name resolves to a value symbol. The dotted name is a member select.
    // 2. The name resolves to a local scope. The dotted name is a hierarchical reference.
    // 3. The name resolves to an imported scope. The dotted name is a hierarchical reference,
    //    but with an added restriction that only a direct downward lookup from the package is
    //    allowed.
    // 4. The name is not found; it's considered a hierarchical reference and participates in
    //    upwards name resolution.
    if (result.found && result.found->isValue()) {
        if (selectors) {
            result.selectors.appendRange(*selectors);
            selectors = nullptr;
        }

        // This is a dotted member access.
        for (const auto& part : nameParts) {
            switch (part.name->kind) {
                case SyntaxKind::IdentifierName:
                    nameToken = part.name->as<IdentifierNameSyntax>().identifier;
                    break;
                case SyntaxKind::IdentifierSelectName: {
                    const auto& idSelect = part.name->as<IdentifierSelectNameSyntax>();
                    nameToken = idSelect.identifier;
                    selectors = &idSelect.selectors;
                    break;
                }
                default:
                    THROW_UNREACHABLE;
            }

            result.selectors.append(LookupResult::MemberSelector{
                nameToken.valueText(), part.dotLocation, nameToken.range() });

            if (selectors)
                result.selectors.appendRange(*selectors);
        }
        return;
    }

    result.isHierarchical = true;
    if (!result.found) {
        // TODO: upward name resolution
        reportUndeclared(nameToken.valueText(), nameToken.range(), flags, result);
        return;
    }

    if (result.found->kind == SymbolKind::InterfacePort) {
        // TODO: modports
        result.isHierarchical = false;
        result.found = result.found->as<InterfacePortSymbol>().connection;
        if (!result.found)
            return;
    }

    if (!result.found->isScope() || result.found->isType()) {
        NamePlusLoc& part = nameParts.back();
        auto& diag = result.addDiag(*this, DiagCode::NotAHierarchicalScope, part.dotLocation);
        diag << nameToken.valueText();
        diag << nameToken.range();
        diag << part.name->sourceRange();

        diag.addNote(DiagCode::NoteDeclarationHere, result.found->location);
        result.found = nullptr;
        return;
    }

    if (result.isHierarchical && (flags & LookupFlags::Constant) != 0) {
        NamePlusLoc& part = nameParts.back();
        auto& diag =
            result.addDiag(*this, DiagCode::HierarchicalNotAllowedInConstant, part.dotLocation);
        diag << nameToken.range();
        result.found = nullptr;
        return;
    }

    // TODO: handle more cases / error conditions
    auto downward = lookupDownward(nameParts, result.found->as<Scope>());
    result.found = downward.found;
}

void Scope::reportUndeclared(string_view name, SourceRange range, bitmask<LookupFlags> flags,
                             LookupResult& result) const {
    // Attempt to give a more helpful error if the symbol exists in scope but is declared after
    // the lookup location. Only do this if the symbol is of the kind we were expecting to find.
    const Symbol* symbol = nullptr;
    bool usedBeforeDeclared = false;
    if ((flags & LookupFlags::AllowDeclaredAfter) == 0) {
        auto scope = this;
        do {
            symbol = scope->find(name);
            if (symbol) {
                if (flags & LookupFlags::Type)
                    usedBeforeDeclared = symbol->isType();
                else
                    usedBeforeDeclared = symbol->isValue();
                break;
            }

            scope = scope->getParent();
        } while (scope);
    }

    if (!usedBeforeDeclared) {
        result.addDiag(*this, DiagCode::UndeclaredIdentifier, range) << name;
    }
    else {
        auto& diag = result.addDiag(*this, DiagCode::UsedBeforeDeclared, range);
        diag << name;
        diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
    }
}

void Scope::DeferredMemberData::addMember(Symbol* symbol) {
    std::get<0>(membersOrStatement).emplace_back(symbol);
}

span<Symbol* const> Scope::DeferredMemberData::getMembers() const {
    return std::get<0>(membersOrStatement);
}

bool Scope::DeferredMemberData::hasStatement() const {
    return membersOrStatement.index() == 1;
}

void Scope::DeferredMemberData::setStatement(StatementBodiedScope& stmt) {
    membersOrStatement = &stmt;
}

StatementBodiedScope* Scope::DeferredMemberData::getStatement() const {
    return std::get<1>(membersOrStatement);
}

void Scope::DeferredMemberData::setPortConnections(
    const SeparatedSyntaxList<PortConnectionSyntax>& connections) {
    portConns = &connections;
}

void Scope::DeferredMemberData::registerTransparentType(const Symbol* insertion,
                                                        const Symbol& parent) {
    transparentTypes.emplace(insertion, &parent);
}

iterator_range<Scope::DeferredMemberData::TransparentTypeMap::const_iterator> Scope::
    DeferredMemberData::getTransparentTypes() const {
    return { transparentTypes.begin(), transparentTypes.end() };
}

void Scope::DeferredMemberData::addForwardingTypedef(const ForwardingTypedefSymbol& symbol) {
    forwardingTypedefs.push_back(&symbol);
}

span<const ForwardingTypedefSymbol* const> Scope::DeferredMemberData::getForwardingTypedefs()
    const {

    return forwardingTypedefs;
}

void Scope::DeferredMemberData::addPortDeclaration(const PortDeclarationSyntax& syntax) {
    portDecls.push_back(&syntax);
}

span<const PortDeclarationSyntax* const> Scope::DeferredMemberData::getPortDeclarations() const {
    return portDecls;
}

} // namespace slang
