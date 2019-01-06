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

const Scope* getLookupParent(const Symbol& symbol) {
    if (InstanceSymbol::isKind(symbol.kind))
        return symbol.as<InstanceSymbol>().definition.getScope();
    else
        return symbol.getScope();
}

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
    selectors.clear();
    diagnostics.clear();
}

void LookupResult::copyFrom(const LookupResult& other) {
    found = other.found;
    systemSubroutine = other.systemSubroutine;
    wasImported = other.wasImported;
    isHierarchical = other.isHierarchical;

    selectors.clear();
    selectors.appendRange(other.selectors);

    diagnostics.clear();
    diagnostics.appendRange(other.diagnostics);
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
        case SyntaxKind::ThisHandle: // TODO: handle this
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
    if (name.empty())
        return nullptr;

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
                    else
                        portMap = const_cast<SymbolMap*>(&sym.as<InstanceSymbol>().getPortMap());

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

    // Continue up the scope chain via our parent. If we hit an instance, we need to instead search
    // within the context of the definition's parent scope.
    auto nextScope = getLookupParent(asSymbol());
    if (!nextScope)
        return;

    location = LookupLocation::after(asSymbol());
    return nextScope->lookupUnqualifiedImpl(name, location, sourceRange, flags, result);
}

namespace {

using namespace slang;

struct NamePlusLoc {
    const NameSyntax* name;
    SourceLocation dotLocation;
};

using NameComponent = std::tuple<Token, const SyntaxList<ElementSelectSyntax>*>;

NameComponent decomposeName(const NameSyntax& name) {
    switch (name.kind) {
        case SyntaxKind::IdentifierName:
            return { name.as<IdentifierNameSyntax>().identifier, nullptr };
        case SyntaxKind::IdentifierSelectName: {
            auto& idSelect = name.as<IdentifierSelectNameSyntax>();
            return { idSelect.identifier, &idSelect.selectors };
        }
        case SyntaxKind::UnitScope:
        case SyntaxKind::RootScope:
        case SyntaxKind::LocalScope:
        case SyntaxKind::ThisHandle:
        case SyntaxKind::SuperHandle:
        case SyntaxKind::ArrayUniqueMethod:
        case SyntaxKind::ArrayAndMethod:
        case SyntaxKind::ArrayOrMethod:
        case SyntaxKind::ArrayXorMethod:
        case SyntaxKind::ConstructorName: {
            auto& keywordName = name.as<KeywordNameSyntax>();
            return { keywordName.keyword, nullptr };
        }
        default:
            THROW_UNREACHABLE;
    }
}

const Symbol* handleLookupSelectors(const Symbol* symbol,
                                    const SyntaxList<ElementSelectSyntax>& selectors,
                                    const BindContext& context, LookupResult& result) {
    ASSERT(symbol);
    if (selectors.empty())
        return symbol;

    for (const ElementSelectSyntax* syntax : selectors) {
        if (!syntax->selector || syntax->selector->kind != SyntaxKind::BitSelect) {
            result.addDiag(context.scope, DiagCode::InvalidScopeIndexExpression,
                           syntax->sourceRange());
            return nullptr;
        }

        auto index = context.evalInteger(*syntax->selector->as<BitSelectSyntax>().expr);
        if (!index)
            return nullptr;

        switch (symbol->kind) {
            case SymbolKind::InstanceArray: {
                auto& array = symbol->as<InstanceArraySymbol>();
                if (!array.range.containsPoint(*index)) {
                    auto& diag = result.addDiag(context.scope, DiagCode::ScopeIndexOutOfRange,
                                                syntax->sourceRange());
                    diag << *index;
                    diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
                }

                symbol = array.elements[array.range.translateIndex(*index)];
                break;
            }
            case SymbolKind::GenerateBlockArray:
                // TODO: handle this
            default: {
                // I think it's safe to assume that the symbol name here will not be empty
                // because if it was, it'd be an instance array or generate array.
                auto& diag = result.addDiag(context.scope, DiagCode::ScopeNotIndexable,
                                            syntax->sourceRange());
                diag << symbol->name;
                diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
                return nullptr;
            }
        }
    }

    return symbol;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be aborted.
bool lookupDownward(span<const NamePlusLoc> nameParts, Token nameToken,
                    const SyntaxList<ElementSelectSyntax>* selectors, const BindContext& context,
                    LookupResult& result, bitmask<LookupFlags> flags) {
    const Symbol* symbol = std::exchange(result.found, nullptr);
    ASSERT(symbol);

    // Loop through each dotted name component and try to find it in the preceeding scope.
    for (auto it = nameParts.rbegin(); it != nameParts.rend(); it++) {
        // If we found a value, the remaining dots are member access expressions.
        if (symbol->isValue()) {
            if (selectors) {
                result.selectors.appendRange(*selectors);
                selectors = nullptr;
            }

            for (; it != nameParts.rend(); it++) {
                std::tie(nameToken, selectors) = decomposeName(*it->name);

                result.selectors.append(LookupResult::MemberSelector{
                    nameToken.valueText(), it->dotLocation, nameToken.range() });

                if (selectors)
                    result.selectors.appendRange(*selectors);
            }

            result.found = symbol;
            return true;
        }

        // This is a hierarchical lookup unless it's the first component in the path and the
        // current scope is either an interface port or a package.
        result.isHierarchical = true;
        if (it == nameParts.rbegin()) {
            result.isHierarchical = symbol->kind != SymbolKind::InterfacePort &&
                                    symbol->kind != SymbolKind::Package &&
                                    symbol->kind != SymbolKind::CompilationUnit;
        }

        if (symbol->kind == SymbolKind::InterfacePort) {
            // TODO: modports
            symbol = symbol->as<InterfacePortSymbol>().connection;
            if (!symbol)
                return false;
        }

        if (!symbol->isScope() || symbol->isType()) {
            auto& diag =
                result.addDiag(context.scope, DiagCode::NotAHierarchicalScope, it->dotLocation);
            diag << nameToken.valueText();
            diag << nameToken.range();
            diag << it->name->sourceRange();

            diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
            return true;
        }

        if (result.isHierarchical && (flags & LookupFlags::Constant) != 0) {
            auto& diag = result.addDiag(context.scope, DiagCode::HierarchicalNotAllowedInConstant,
                                        it->dotLocation);
            diag << nameToken.range();
            return false;
        }

        if (selectors) {
            symbol = handleLookupSelectors(symbol, *selectors, context, result);
            if (!symbol)
                return true;
        }

        SymbolKind previousKind = symbol->kind;
        string_view packageName = symbol->kind == SymbolKind::Package ? symbol->name : "";
        const Scope& current = symbol->as<Scope>();

        std::tie(nameToken, selectors) = decomposeName(*it->name);
        if (nameToken.valueText().empty())
            return false;

        symbol = current.find(nameToken.valueText());
        if (!symbol) {
            // Give a slightly nicer error if this is the first component in a package lookup.
            DiagCode code = DiagCode::CouldNotResolveHierarchicalPath;
            if (!packageName.empty())
                code = DiagCode::UnknownPackageMember;
            else if (previousKind == SymbolKind::CompilationUnit)
                code = DiagCode::UnknownUnitMember;

            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << nameToken.valueText();
            diag << nameToken.range();

            if (!packageName.empty())
                diag << packageName;

            return true;
        }
    }

    result.found = symbol;
    if (selectors)
        result.selectors.appendRange(*selectors);

    return true;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be aborted.
bool lookupUpward(Compilation& compilation, string_view name, span<const NamePlusLoc> nameParts,
                  Token nameToken, const SyntaxList<ElementSelectSyntax>* selectors,
                  const BindContext& context, LookupResult& result, bitmask<LookupFlags> flags) {

    // Upward lookups can match either a scope name, or a module definition name (on any of the
    // instances). Imports are not considered.
    const Scope* scope = &context.scope;
    while (true) {
        const Scope* nextInstance = nullptr;

        while (scope) {
            auto symbol = scope->find(name);
            if (!symbol || symbol->isValue() || symbol->isType() || !symbol->isScope()) {
                // We didn't find an instance name, so now look at the definition types of each
                // instance.
                symbol = nullptr;
                for (auto& instance : scope->membersOfType<InstanceSymbol>()) {
                    if (instance.definition.name == name) {
                        if (!symbol)
                            symbol = &instance;
                        else {
                            // TODO: error
                        }
                    }
                }
            }

            if (symbol) {
                result.clear();
                result.found = symbol;

                if (!lookupDownward(nameParts, nameToken, selectors, context, result, flags))
                    return false;

                if (result.found)
                    return true;
            }

            // Figure out which scope to look at next. If we're already at the root scope, we're
            // done and should return. Otherwise, we want to keep going up until we hit the
            // compilation unit, at which point we'll jump back to the instantiation scope of the
            // last instance we hit.
            symbol = &scope->asSymbol();
            switch (symbol->kind) {
                case SymbolKind::Root:
                    return true;
                case SymbolKind::Definition:
                    return false;
                case SymbolKind::CompilationUnit:
                    scope = nullptr;
                    break;
                case SymbolKind::ModuleInstance:
                case SymbolKind::InterfaceInstance:
                case SymbolKind::Program:
                    nextInstance = symbol->getScope();
                    scope = symbol->as<InstanceSymbol>().definition.getScope();
                    break;
                default:
                    scope = symbol->getScope();
                    break;
            }
        }

        if (nextInstance)
            scope = nextInstance;
        else
            scope = &compilation.getRoot();
    }
}

const Symbol* getCompilationUnit(const Symbol& symbol) {
    const Symbol* current = &symbol;
    while (true) {
        if (current->kind == SymbolKind::CompilationUnit)
            return current;

        auto scope = getLookupParent(*current);
        if (!scope)
            return nullptr;

        current = &scope->asSymbol();
    }
}

} // namespace

void Scope::lookupQualified(const ScopedNameSyntax& syntax, LookupLocation location,
                            bitmask<LookupFlags> flags, LookupResult& result) const {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    // TODO: clean up dot vs colon handling
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

    auto [nameToken, selectors] = decomposeName(*scoped->left);
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    auto downward = [&, nameToken = nameToken, selectors = selectors]() {
        return lookupDownward(nameParts, nameToken, selectors, BindContext(*this, location), result,
                              flags);
    };

    bool inConstantEval = (flags & LookupFlags::Constant) != 0 || compilation.isFinalizing();

    switch (scoped->left->kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
            break;
        case SyntaxKind::UnitScope:
            result.found = getCompilationUnit(asSymbol());
            downward();
            return;
        case SyntaxKind::RootScope:
            // Be careful to avoid calling getRoot() if we're in a constant context (there's a
            // chance we could already be in the middle of calling getRoot in that case).
            if (inConstantEval) {
                result.addDiag(*this, DiagCode::HierarchicalNotAllowedInConstant,
                               nameToken.range());
                return;
            }

            result.found = &compilation.getRoot();
            downward();
            return;
        case SyntaxKind::LocalScope: // TODO: handle these
        case SyntaxKind::ThisHandle:
        case SyntaxKind::SuperHandle:
        default:
            THROW_UNREACHABLE;
    }

    // Start by trying to find the first name segment using normal unqualified lookup
    lookupUnqualifiedImpl(name, location, nameToken.range(), flags, result);
    if (result.hasError())
        return;

    // [23.7.1] If we are starting with a colon separator, always do a downwards name resolution.
    if (colonParts) {
        // If the prefix name can be resolved normally, we have a class scope, otherwise it's a
        // package lookup.
        if (!result.found) {
            result.found = compilation.getPackage(name);

            if (!result.found) {
                result.addDiag(*this, DiagCode::UnknownClassOrPackage, nameToken.range()) << name;
                return;
            }
        }

        // We can't do upwards name resolution if colon access is involved, so always return after
        // one downward lookup.
        downward();
        return;
    }

    // [23.7] lists the possible cases for dotted names:
    // 1. The name resolves to a value symbol. The dotted name is a member select.
    // 2. The name resolves to a local scope. The dotted name is a hierarchical reference.
    // 3. The name resolves to an imported scope. The dotted name is a hierarchical reference,
    //    but with an added restriction that only a direct downward lookup from the package is
    //    allowed.
    // 4. The name is not found; it's considered a hierarchical reference and participates in
    //    upwards name resolution.

    LookupResult originalResult;
    if (result.found) {
        // Perform the downward lookup.
        if (!downward())
            return;

        // If we found a symbol, we're done with lookup. In case (1) above we'll always have a
        // found symbol here. Otherwise, if we're in case (2) we need to do further upwards name
        // lookup. If we're in case (3) we've already issued an error and just need to give up.
        if (result.found || result.wasImported)
            return;

        if (inConstantEval) {
            result.addDiag(*this, DiagCode::HierarchicalNotAllowedInConstant, nameToken.range());
            return;
        }

        originalResult.copyFrom(result);
    }
    else if (inConstantEval) {
        // We can't perform upward lookups during constant evaluation so just report an unknown
        // identifier.
        reportUndeclared(name, nameToken.range(), flags, result);
        return;
    }

    // If we reach this point we're in case (2) or (4) above. Go up through the instantiation
    // hierarchy and see if we can find a match there.
    if (!lookupUpward(compilation, name, nameParts, nameToken, selectors,
                      BindContext(*this, location), result, flags)) {
        return;
    }
    if (result.found)
        return;

    // We couldn't find anything. originalResult has any diagnostics issued by the first downward
    // lookup (if any), so it's fine to just return it as is. If we never found any symbol
    // originally, issue an appropriate error for that.
    result.copyFrom(originalResult);
    if (!result.found && !result.hasError())
        reportUndeclared(name, nameToken.range(), flags, result);
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
