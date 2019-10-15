//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/Scope.h"

#include "slang/binding/Expressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/syntax/AllSyntax.h"
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

Scope::Scope(Compilation& compilation_, const Symbol* thisSym_) :
    compilation(compilation_), thisSym(thisSym_), nameMap(compilation.allocSymbolMap()) {
}

Scope::iterator& Scope::iterator::operator++() {
    current = current->nextInScope;
    return *this;
}

const NetType& Scope::getDefaultNetType() const {
    const Scope* current = this;
    while (current) {
        auto& sym = current->asSymbol();
        switch (sym.kind) {
            case SymbolKind::Definition:
                return sym.as<DefinitionSymbol>().defaultNetType;
            case SymbolKind::Package:
                return sym.as<PackageSymbol>().defaultNetType;
            default:
                if (InstanceSymbol::isKind(sym.kind))
                    current = &sym.as<InstanceSymbol>().definition;
                else
                    current = sym.getParentScope();
                break;
        }
    }

    return getCompilation().getNetType(TokenKind::Unknown);
}

TimeScale Scope::getTimeScale() const {
    const Scope* current = this;
    while (current) {
        auto& sym = current->asSymbol();
        switch (sym.kind) {
            case SymbolKind::CompilationUnit:
                return sym.as<CompilationUnitSymbol>().getTimeScale();
            case SymbolKind::Definition:
                return sym.as<DefinitionSymbol>().getTimeScale();
            case SymbolKind::Package:
                return sym.as<PackageSymbol>().getTimeScale();
            default:
                if (InstanceSymbol::isKind(sym.kind))
                    current = &sym.as<InstanceSymbol>().definition;
                else
                    current = sym.getParentScope();
                break;
        }
    }

    return getCompilation().getDefaultTimeScale();
}

Diagnostic& Scope::addDiag(DiagCode code, SourceLocation location) const {
    return compilation.diags.add(*thisSym, code, location);
}

Diagnostic& Scope::addDiag(DiagCode code, SourceRange sourceRange) const {
    return compilation.diags.add(*thisSym, code, sourceRange);
}

void Scope::addDiags(const Diagnostics& diags) const {
    for (auto& diag : diags) {
        Diagnostic copy = diag;
        copy.symbol = thisSym;
        compilation.diags.append(copy);
    }
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

    insertMember(&symbol, lastMember, false);
}

void Scope::addMembers(const SyntaxNode& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration: {
            // Definitions exist in their own namespace and are tracked in the Compilation.
            auto& def = DefinitionSymbol::fromSyntax(compilation,
                                                     syntax.as<ModuleDeclarationSyntax>(), *this);
            addMember(def);
            compilation.addDefinition(def);
            break;
        }
        case SyntaxKind::PackageDeclaration: {
            // Packages exist in their own namespace and are tracked in the Compilation.
            auto& package =
                PackageSymbol::fromSyntax(compilation, syntax.as<ModuleDeclarationSyntax>(), *this);
            addMember(package);
            compilation.addPackage(package);
            break;
        }
        case SyntaxKind::PackageImportDeclaration: {
            auto& importDecl = syntax.as<PackageImportDeclarationSyntax>();
            for (auto item : importDecl.items) {
                if (item->item.kind == TokenKind::Star) {
                    addWildcardImport(*item, importDecl.attributes);
                }
                else {
                    auto import = compilation.emplace<ExplicitImportSymbol>(
                        item->package.valueText(), item->item.valueText(), item->item.location());

                    import->setSyntax(*item);
                    addMember(*import);
                    compilation.addAttributes(*import, importDecl.attributes);
                }
            }
            break;
        }
        case SyntaxKind::HierarchyInstantiation:
        case SyntaxKind::AnsiPortList:
        case SyntaxKind::NonAnsiPortList:
        case SyntaxKind::IfGenerate:
        case SyntaxKind::CaseGenerate:
        case SyntaxKind::LoopGenerate: {
            auto sym = compilation.emplace<DeferredMemberSymbol>(syntax);
            addMember(*sym);
            getOrAddDeferredData().addMember(sym);
            break;
        }
        case SyntaxKind::PortDeclaration:
            getOrAddDeferredData().addPortDeclaration(syntax.as<PortDeclarationSyntax>());
            break;
        case SyntaxKind::ModportDeclaration: {
            SmallVectorSized<const ModportSymbol*, 16> results;
            ModportSymbol::fromSyntax(compilation, syntax.as<ModportDeclarationSyntax>(), results);
            for (auto symbol : results)
                addMember(*symbol);
            break;
        }
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            addMember(SubroutineSymbol::fromSyntax(compilation,
                                                   syntax.as<FunctionDeclarationSyntax>(), *this));
            break;
        case SyntaxKind::DataDeclaration: {
            // If this is a simple identifier type, we have no choice but to defer symbol creation
            // because it could turn out to be a net or a variable.
            auto& dataDecl = syntax.as<DataDeclarationSyntax>();
            if (!getSimpleTypeName(*dataDecl.type).empty()) {
                auto sym = compilation.emplace<DeferredMemberSymbol>(syntax);
                addMember(*sym);
                getOrAddDeferredData().addMember(sym);
            }
            else {
                SmallVectorSized<const ValueSymbol*, 4> symbols;
                VariableSymbol::fromSyntax(compilation, dataDecl, *this, symbols);
                for (auto symbol : symbols)
                    addMember(*symbol);
            }
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
            auto& statement = syntax.as<ParameterDeclarationStatementSyntax>();
            auto paramBase = statement.parameter;
            if (paramBase->kind == SyntaxKind::ParameterDeclaration) {
                SmallVectorSized<ParameterSymbol*, 8> params;
                ParameterSymbol::fromSyntax(*this, paramBase->as<ParameterDeclarationSyntax>(),
                                            /* isLocal */ true, /* isPort */ false, params);
                for (auto param : params) {
                    compilation.addAttributes(*param, statement.attributes);
                    addMember(*param);
                }
            }
            else {
                SmallVectorSized<TypeParameterSymbol*, 8> params;
                TypeParameterSymbol::fromSyntax(*this,
                                                paramBase->as<TypeParameterDeclarationSyntax>(),
                                                /* isLocal */ true, /* isPort */ false, params);
                for (auto param : params) {
                    compilation.addAttributes(*param, statement.attributes);
                    addMember(*param);
                }
            }
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
            span<const StatementBlockSymbol* const> additional;
            auto& block = ProceduralBlockSymbol::fromSyntax(
                *this, syntax.as<ProceduralBlockSyntax>(), additional);

            for (auto b : additional)
                addMember(*b);
            addMember(block);
            break;
        }
        case SyntaxKind::EmptyMember:
            addMember(
                EmptyMemberSymbol::fromSyntax(compilation, *this, syntax.as<EmptyMemberSyntax>()));
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
        case SyntaxKind::ContinuousAssign: {
            SmallVectorSized<const ContinuousAssignSymbol*, 16> results;
            ContinuousAssignSymbol::fromSyntax(compilation, syntax.as<ContinuousAssignSyntax>(),
                                               results);
            for (auto symbol : results)
                addMember(*symbol);
            break;
        }
        case SyntaxKind::NetTypeDeclaration:
            addMember(NetType::fromSyntax(compilation, syntax.as<NetTypeDeclarationSyntax>()));
            break;
        case SyntaxKind::TimeUnitsDeclaration:
            // These are handled elsewhere; just ignore here.
            break;
        case SyntaxKind::GenvarDeclaration: {
            SmallVectorSized<const GenvarSymbol*, 16> genvars;
            GenvarSymbol::fromSyntax(compilation, syntax.as<GenvarDeclarationSyntax>(), genvars);
            for (auto genvar : genvars)
                addMember(*genvar);
            break;
        }
        default:
            addDiag(diag::NotYetSupported, syntax.sourceRange());
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
        case SymbolKind::ForwardingTypedef:
            return nullptr;
        case SymbolKind::TransparentMember:
            return &symbol->as<TransparentMemberSymbol>().wrapped;
        default:
            return symbol;
    }
}

Scope::DeferredMemberData& Scope::getOrAddDeferredData() const {
    return compilation.getOrAddDeferredData(deferredMemberIndex);
}

void Scope::insertMember(const Symbol* member, const Symbol* at, bool isElaborating) const {
    ASSERT(!member->parentScope);
    ASSERT(!member->nextInScope);

    if (!at) {
        member->indexInScope = SymbolIndex{ 1 };
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
        member->kind != SymbolKind::Definition && member->kind != SymbolKind::Package) {
        auto pair = nameMap->emplace(member->name, member);
        if (!pair.second)
            handleNameConflict(*member, pair.first->second, isElaborating);
    }
}

void Scope::handleNameConflict(const Symbol& member, const Symbol*& existing,
                               bool isElaborating) const {
    // We have a name collision; first check if this is ok (forwarding typedefs share a
    // name with the actual typedef) and if not give the user a helpful error message.
    if (existing->kind == SymbolKind::TypeAlias && member.kind == SymbolKind::ForwardingTypedef) {
        // Just add this forwarding typedef to a deferred list so we can process them
        // once we know the kind of symbol the alias points to.
        existing->as<TypeAliasType>().addForwardDecl(member.as<ForwardingTypedefSymbol>());
        return;
    }

    if (existing->kind == SymbolKind::ForwardingTypedef &&
        member.kind == SymbolKind::ForwardingTypedef) {
        // Found another forwarding typedef; link it to the previous one.
        existing->as<ForwardingTypedefSymbol>().addForwardDecl(
            member.as<ForwardingTypedefSymbol>());
        return;
    }

    if (existing->kind == SymbolKind::ForwardingTypedef && member.kind == SymbolKind::TypeAlias) {
        // We found the actual type for a previous forwarding declaration. Replace it in
        // the name map.
        member.as<TypeAliasType>().addForwardDecl(existing->as<ForwardingTypedefSymbol>());
        existing = &member;
        return;
    }

    if (existing->kind == SymbolKind::ExplicitImport && member.kind == SymbolKind::ExplicitImport &&
        existing->as<ExplicitImportSymbol>().packageName ==
            member.as<ExplicitImportSymbol>().packageName) {
        // Duplicate explicit imports are specifically allowed,
        // so just ignore the other one (with a warning).
        auto& diag = addDiag(diag::DuplicateImport, member.location);
        diag.addNote(diag::NotePreviousDefinition, existing->location);
        return;
    }

    if (existing->kind == SymbolKind::GenerateBlock && member.kind == SymbolKind::GenerateBlock) {
        // If both are generate blocks and both are from the same generate construct, it's ok
        // for them to have the same name. We take the one that is instantiated.
        auto& gen1 = existing->as<GenerateBlockSymbol>();
        auto& gen2 = member.as<GenerateBlockSymbol>();
        if (gen1.constructIndex == gen2.constructIndex) {
            ASSERT(!(gen1.isInstantiated && gen2.isInstantiated));
            if (gen2.isInstantiated)
                existing = &member;
            return;
        }
    }

    if (!isElaborating && existing->isValue() && member.isValue()) {
        // We want to look at the symbol types here to provide nicer error messages, but
        // it might not be safe to resolve the type at this point (because we're in the
        // middle of elaborating the scope). Save the member for later reporting.
        getOrAddDeferredData().addNameConflict(member);
        return;
    }

    reportNameConflict(member, *existing);
}

void Scope::reportNameConflict(const Symbol& member, const Symbol& existing) const {
    Diagnostic* diag;
    if (existing.isValue() && member.isValue()) {
        const Type& memberType = member.as<ValueSymbol>().getType();
        const Type& existingType = existing.as<ValueSymbol>().getType();

        if (memberType.isError() || existingType.isError() || memberType.isMatching(existingType)) {
            diag = &addDiag(diag::Redefinition, member.location);
            (*diag) << member.name;
        }
        else {
            diag = &addDiag(diag::RedefinitionDifferentType, member.location);
            (*diag) << member.name << memberType << existingType;
        }
    }
    else if (existing.kind != member.kind) {
        diag = &addDiag(diag::RedefinitionDifferentSymbolKind, member.location);
        (*diag) << member.name;
    }
    else {
        diag = &addDiag(diag::Redefinition, member.location);
        (*diag) << member.name;
    }
    diag->addNote(diag::NotePreviousDefinition, existing.location);
}

SymbolIndex Scope::getInsertionIndex(const Symbol& at) const {
    return SymbolIndex{ (uint32_t)at.indexInScope + (&at == lastMember) };
}

void Scope::elaborate() const {
    ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto deferredData = compilation.getOrAddDeferredData(deferredMemberIndex);
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    for (auto member : deferredData.getNameConflicts()) {
        auto existing = nameMap->find(member->name)->second;
        reportNameConflict(*member, *existing);
    }

    SmallSet<const SyntaxNode*, 8> enumDecls;
    for (const auto& pair : deferredData.getTransparentTypes()) {
        const Symbol* insertAt = pair.first;
        const Type& type = pair.second->getDeclaredType()->getType();

        if (type.kind == SymbolKind::EnumType) {
            if (!type.getSyntax() || enumDecls.insert(type.getSyntax()).second) {
                for (const auto& value : type.as<EnumType>().values()) {
                    auto wrapped = compilation.emplace<TransparentMemberSymbol>(value);
                    insertMember(wrapped, insertAt, true);
                    insertAt = wrapped;
                }
            }
        }
    }

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
                                           member.node.as<HierarchyInstantiationSyntax>(), location,
                                           *this, instances);

                const Symbol* last = symbol;
                for (auto instance : instances) {
                    insertMember(instance, last, true);
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
                    insertMember(port, last, true);
                    last = port;

                    if (port->kind == SymbolKind::Port) {
                        auto& valuePort = port->as<PortSymbol>();
                        if (valuePort.internalSymbol &&
                            !valuePort.internalSymbol->getParentScope()) {
                            insertMember(valuePort.internalSymbol, last, true);
                            last = valuePort.internalSymbol;
                        }
                    }
                }

                // If we have port connections, tie them to the ports now.
                if (auto connections = deferredData.getPortConnections())
                    PortSymbol::makeConnections(*this, ports, *connections);

                break;
            }
            case SyntaxKind::DataDeclaration: {
                SmallVectorSized<const ValueSymbol*, 4> symbols;
                VariableSymbol::fromSyntax(compilation, member.node.as<DataDeclarationSyntax>(),
                                           *this, symbols);

                const Symbol* last = symbol;
                for (auto var : symbols) {
                    insertMember(var, last, true);
                    last = var;
                }
                break;
            }
            default:
                break;
        }
    }

    // Now that all instances have been inserted, go back through and elaborate generate
    // blocks. The spec requires that we give each generate construct an index, starting
    // from one. This index is used to generate external names for unnamed generate blocks.
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
                    insertMember(block, last, true);
                    last = block;
                }
                break;
            }
            case SyntaxKind::CaseGenerate: {
                SmallVectorSized<GenerateBlockSymbol*, 8> blocks;
                GenerateBlockSymbol::fromSyntax(compilation, member.node.as<CaseGenerateSyntax>(),
                                                location, *this, constructIndex, true, blocks);

                const Symbol* last = symbol;
                for (auto block : blocks) {
                    insertMember(block, last, true);
                    last = block;
                }
                break;
            }
            case SyntaxKind::LoopGenerate:
                insertMember(&GenerateBlockArraySymbol::fromSyntax(
                                 compilation, member.node.as<LoopGenerateSyntax>(),
                                 getInsertionIndex(*symbol), location, *this, constructIndex),
                             symbol, true);
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
            addDiag(diag::UnresolvedForwardTypedef, symbol->location) << symbol->name;
    }

    ASSERT(deferredMemberIndex == DeferredMemberIndex::Invalid);
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
                    auto& diag = result.addDiag(*this, diag::RecursiveDefinition, sourceRange)
                                 << name;
                    diag.addNote(diag::NoteDeclarationHere, result.found->location);
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
        if (!package) {
            result.sawBadImport = true;
            continue;
        }

        const Symbol* imported = package->find(name);
        if (imported)
            imports.emplace(Import{ imported, import });
    }

    if (!imports.empty()) {
        if (imports.size() > 1) {
            auto& diag = result.addDiag(*this, diag::AmbiguousWildcardImport, sourceRange) << name;
            for (const auto& pair : imports) {
                diag.addNote(diag::NoteImportedFrom, pair.import->location);
                diag.addNote(diag::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            auto& diag = result.addDiag(*this, diag::ImportNameCollision, sourceRange) << name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            diag.addNote(diag::NoteImportedFrom, imports[0].import->location);
            diag.addNote(diag::NoteDeclarationHere, imports[0].imported->location);
        }

        result.wasImported = true;
        result.found = imports[0].imported;
        return;
    }

    // Continue up the scope chain via our parent. If we hit an instance, we need to instead
    // search within the context of the definition's parent scope.
    const Scope* nextScope;
    if (InstanceSymbol::isKind(asSymbol().kind)) {
        auto& def = asSymbol().as<InstanceSymbol>().definition;
        nextScope = def.getParentScope();
        location = LookupLocation(nextScope, (uint32_t)def.getIndex() + 1);
    }
    else {
        nextScope = asSymbol().getParentScope();
        location = LookupLocation(nextScope, (uint32_t)asSymbol().getIndex() + 1);
    }

    if (!nextScope)
        return;

    return nextScope->lookupUnqualifiedImpl(name, location, sourceRange, flags, result);
}

const Symbol* Scope::selectChild(const Symbol& initialSymbol,
                                 span<const ElementSelectSyntax* const> selectors,
                                 const BindContext& context, LookupResult& result) {
    const Symbol* symbol = &initialSymbol;
    for (const ElementSelectSyntax* syntax : selectors) {
        if (!syntax->selector || syntax->selector->kind != SyntaxKind::BitSelect) {
            result.addDiag(context.scope, diag::InvalidScopeIndexExpression, syntax->sourceRange());
            return nullptr;
        }

        auto index = context.evalInteger(*syntax->selector->as<BitSelectSyntax>().expr);
        if (!index)
            return nullptr;

        switch (symbol->kind) {
            case SymbolKind::InstanceArray: {
                auto& array = symbol->as<InstanceArraySymbol>();
                if (array.elements.empty())
                    return nullptr;

                if (!array.range.containsPoint(*index)) {
                    auto& diag = result.addDiag(context.scope, diag::ScopeIndexOutOfRange,
                                                syntax->sourceRange());
                    diag << *index;
                    diag.addNote(diag::NoteDeclarationHere, symbol->location);
                    return nullptr;
                }

                symbol = array.elements[size_t(array.range.translateIndex(*index))];
                break;
            }
            case SymbolKind::GenerateBlockArray: {
                bool found = false;
                auto& array = symbol->as<GenerateBlockArraySymbol>();
                for (auto& entry : array.entries) {
                    if (*entry.index == *index) {
                        found = true;
                        symbol = entry.block;
                        break;
                    }
                }

                if (!found) {
                    auto& diag = result.addDiag(context.scope, diag::ScopeIndexOutOfRange,
                                                syntax->sourceRange());
                    diag << *index;
                    diag.addNote(diag::NoteDeclarationHere, symbol->location);
                    return nullptr;
                }
                break;
            }
            default: {
                // I think it's safe to assume that the symbol name here will not be empty
                // because if it was, it'd be an instance array or generate array.
                auto& diag =
                    result.addDiag(context.scope, diag::ScopeNotIndexable, syntax->sourceRange());
                diag << symbol->name;
                diag.addNote(diag::NoteDeclarationHere, symbol->location);
                return nullptr;
            }
        }
    }

    return symbol;
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
        case SyntaxKind::SystemName:
            return { name.as<SystemNameSyntax>().systemIdentifier, nullptr };
        case SyntaxKind::IdentifierSelectName: {
            auto& idSelect = name.as<IdentifierSelectNameSyntax>();
            return { idSelect.identifier, &idSelect.selectors };
        }
        case SyntaxKind::ClassName: {
            // TODO: handle class params
            auto& cn = name.as<ClassNameSyntax>();
            return { cn.identifier, nullptr };
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

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
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
        // current scope is either an interface port or a package, or it's an instance that
        // is in the same scope as the lookup.
        result.isHierarchical = true;
        if (it == nameParts.rbegin()) {
            if (symbol->kind == SymbolKind::InstanceArray || InstanceSymbol::isKind(symbol->kind)) {
                result.isHierarchical = symbol->getParentScope() != &context.scope;
            }
            else {
                result.isHierarchical = symbol->kind != SymbolKind::InterfacePort &&
                                        symbol->kind != SymbolKind::Package &&
                                        symbol->kind != SymbolKind::CompilationUnit;
            }
        }

        if (symbol->kind == SymbolKind::InterfacePort) {
            // TODO: modports
            symbol = symbol->as<InterfacePortSymbol>().connection;
            if (!symbol)
                return false;
        }

        if (!symbol->isScope() || symbol->isType()) {
            auto code = symbol->isType() ? diag::DotOnType : diag::NotAHierarchicalScope;
            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << nameToken.range();
            diag << it->name->sourceRange();

            if (!symbol->isType())
                diag << nameToken.valueText();

            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return true;
        }

        if (result.isHierarchical && (flags & LookupFlags::Constant) != 0) {
            auto& diag = result.addDiag(context.scope, diag::HierarchicalNotAllowedInConstant,
                                        it->dotLocation);
            diag << nameToken.range();
            return false;
        }

        if (selectors) {
            symbol = Scope::selectChild(*symbol, *selectors, context, result);
            if (!symbol)
                return false;
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
            DiagCode code = diag::CouldNotResolveHierarchicalPath;
            if (!packageName.empty())
                code = diag::UnknownPackageMember;
            else if (previousKind == SymbolKind::CompilationUnit)
                code = diag::UnknownUnitMember;

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
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
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
            // compilation unit, at which point we'll jump back to the instantiation scope of
            // the last instance we hit.
            symbol = &scope->asSymbol();
            switch (symbol->kind) {
                case SymbolKind::Root:
                    result.clear();
                    return true;
                case SymbolKind::Definition:
                    result.clear();
                    return false;
                case SymbolKind::CompilationUnit:
                    scope = nullptr;
                    break;
                case SymbolKind::ModuleInstance:
                case SymbolKind::InterfaceInstance:
                case SymbolKind::Program:
                    nextInstance = symbol->getParentScope();
                    scope = symbol->getLexicalScope();
                    break;
                default:
                    scope = symbol->getLexicalScope();
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

        auto scope = current->getLexicalScope();
        ASSERT(scope);

        current = &scope->asSymbol();
    }
}

void unwrapResult(LookupResult& result) {
    // Unwrap type parameters into their target type alias.
    if (result.found && result.found->kind == SymbolKind::TypeParameter)
        result.found = &result.found->as<TypeParameterSymbol>().getTypeAlias();
}

} // namespace

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
            unwrapResult(result);
            return;
        case SyntaxKind::ThisHandle:
        case SyntaxKind::ClassName:
            result.addDiag(*this, diag::NotYetSupported, syntax.sourceRange());
            result.found = nullptr;
            return;
        case SyntaxKind::SystemName: {
            // If this is a system name, look up directly in the compilation.
            nameToken = syntax.as<SystemNameSyntax>().systemIdentifier;
            result.found = nullptr;
            result.systemSubroutine = compilation.getSystemSubroutine(nameToken.valueText());
            if (!result.systemSubroutine) {
                result.addDiag(*this, diag::UnknownSystemName, nameToken.range())
                    << nameToken.valueText();
            }
            return;
        }
        default:
            THROW_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    // Perform the lookup.
    lookupUnqualifiedImpl(name, location, nameToken.range(), flags, result);
    if (!result.found && !result.hasError())
        reportUndeclared(name, nameToken.range(), flags, false, result);

    unwrapResult(result);

    if (selectors) {
        // If this is a scope, the selectors should be an index into it.
        if (result.found && result.found->isScope() && !result.found->isType()) {
            result.found =
                selectChild(*result.found, *selectors, BindContext(*this, location), result);
        }
        else {
            result.selectors.appendRange(*selectors);
        }
    }
}

const Symbol* Scope::lookupUnqualifiedName(string_view name, LookupLocation location,
                                           SourceRange sourceRange, bitmask<LookupFlags> flags,
                                           bool errorIfNotFound) const {
    if (name.empty())
        return nullptr;

    LookupResult result;
    lookupUnqualifiedImpl(name, location, sourceRange, flags, result);
    ASSERT(result.selectors.empty());
    unwrapResult(result);

    if (errorIfNotFound && !result.found && !result.hasError())
        reportUndeclared(name, sourceRange, flags, false, result);

    if (result.hasError())
        getCompilation().addDiagnostics(result.getDiagnostics());

    return result.found;
}

const Symbol* Scope::lookupName(string_view name, LookupLocation location,
                                bitmask<LookupFlags> flags) const {
    LookupResult result;
    lookupName(compilation.parseName(name), location, flags, result);
    ASSERT(result.selectors.empty());
    return result.found;
}

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

    if (compilation.isFinalizing())
        flags |= LookupFlags::Constant;

    bool inConstantEval = (flags & LookupFlags::Constant) != 0;

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
                result.isHierarchical = true;
                result.addDiag(*this, diag::HierarchicalNotAllowedInConstant, nameToken.range());
                return;
            }

            result.found = &compilation.getRoot();
            downward();
            return;
        case SyntaxKind::ClassName:
        case SyntaxKind::LocalScope:
        case SyntaxKind::ThisHandle:
        case SyntaxKind::SuperHandle:
            result.addDiag(*this, diag::NotYetSupported, syntax.sourceRange());
            return;
        default:
            THROW_UNREACHABLE;
    }

    // Start by trying to find the first name segment using normal unqualified lookup
    lookupUnqualifiedImpl(name, location, nameToken.range(), flags, result);
    if (result.hasError())
        return;

    // [23.7.1] If we are starting with a colon separator, always do a downwards name
    // resolution.
    if (colonParts) {
        // If the prefix name can be resolved normally, we have a class scope, otherwise it's a
        // package lookup.
        if (!result.found) {
            result.found = compilation.getPackage(name);

            if (!result.found) {
                result.addDiag(*this, diag::UnknownClassOrPackage, nameToken.range()) << name;
                return;
            }
        }

        // We can't do upwards name resolution if colon access is involved, so always return
        // after one downward lookup.
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
            // An appropriate error was already issued in lookupDownward()
            return;
        }

        originalResult.copyFrom(result);
    }
    else if (inConstantEval) {
        // We can't perform upward lookups during constant evaluation so just report an unknown
        // identifier.
        reportUndeclared(name, nameToken.range(), flags, true, result);
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

    // We couldn't find anything. originalResult has any diagnostics issued by the first
    // downward lookup (if any), so it's fine to just return it as is. If we never found any
    // symbol originally, issue an appropriate error for that.
    result.copyFrom(originalResult);
    if (!result.found && !result.hasError())
        reportUndeclared(name, nameToken.range(), flags, true, result);
}

void Scope::reportUndeclared(string_view name, SourceRange range, bitmask<LookupFlags> flags,
                             bool isHierarchical, LookupResult& result) const {
    // If we observed a wildcard import we couldn't resolve, we shouldn't report an
    // error for undeclared identifier because maybe it's supposed to come from that package.
    // In particular it's important that we do this because when we first look at a
    // definition it's possible we haven't seen the file containing the package yet.
    if (result.sawBadImport)
        return;

    // Attempt to give a more helpful error if the symbol exists in scope but is declared after
    // the lookup location. Only do this if the symbol is of the kind we were expecting to find.
    const Symbol* symbol = nullptr;
    bool usedBeforeDeclared = false;
    if ((flags & LookupFlags::AllowDeclaredAfter) == 0) {
        auto scope = this;
        do {
            symbol = scope->find(name);
            if (symbol) {
                if (flags & LookupFlags::Type) {
                    usedBeforeDeclared =
                        symbol->isType() || symbol->kind == SymbolKind::TypeParameter;
                }
                else {
                    usedBeforeDeclared = symbol->isValue() ||
                                         symbol->kind == SymbolKind::InstanceArray ||
                                         symbol->kind == SymbolKind::InterfaceInstance;
                }
                break;
            }

            scope = scope->asSymbol().getLexicalScope();
        } while (scope);
    }

    if (!usedBeforeDeclared) {
        auto& diag = result.addDiag(*this, diag::UndeclaredIdentifier, range) << name;
        if (isHierarchical && (flags & LookupFlags::Constant))
            diag.addNote(diag::NoteHierarchicalNameInCE, range.start()) << name;
    }
    else {
        auto& diag = result.addDiag(*this, diag::UsedBeforeDeclared, range);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, symbol->location);
    }
}

void Scope::addWildcardImport(const PackageImportItemSyntax& item,
                              span<const AttributeInstanceSyntax* const> attributes) {
    // Check for redundant import statements.
    for (auto import : compilation.queryImports(importDataIndex)) {
        if (import->packageName == item.package.valueText()) {
            if (!import->packageName.empty()) {
                auto& diag = addDiag(diag::DuplicateImport, item.item.location());
                diag.addNote(diag::NotePreviousDefinition, import->location);
            }
            return;
        }
    }

    auto import =
        compilation.emplace<WildcardImportSymbol>(item.package.valueText(), item.item.location());

    import->setSyntax(item);
    addMember(*import);
    compilation.trackImport(importDataIndex, *import);
    compilation.addAttributes(*import, attributes);
}

void Scope::DeferredMemberData::addMember(Symbol* symbol) {
    members.emplace_back(symbol);
}

span<Symbol* const> Scope::DeferredMemberData::getMembers() const {
    return members;
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

void Scope::DeferredMemberData::addNameConflict(const Symbol& member) {
    nameConflicts.push_back(&member);
}

span<const Symbol* const> Scope::DeferredMemberData::getNameConflicts() const {
    return nameConflicts;
}

} // namespace slang
