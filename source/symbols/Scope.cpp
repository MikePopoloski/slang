//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/Scope.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"
#include "slang/types/NetType.h"
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
    do {
        auto& sym = current->asSymbol();
        switch (sym.kind) {
            case SymbolKind::Package:
                return sym.as<PackageSymbol>().defaultNetType;
            default:
                if (sym.kind == SymbolKind::InstanceBody)
                    return sym.as<InstanceBodySymbol>().getDefinition().defaultNetType;
                else
                    current = sym.getParentScope();
                break;
        }
    } while (current);

    return getCompilation().getNetType(TokenKind::Unknown);
}

TimeScale Scope::getTimeScale() const {
    const Scope* current = this;
    do {
        auto& sym = current->asSymbol();
        switch (sym.kind) {
            case SymbolKind::CompilationUnit:
                return sym.as<CompilationUnitSymbol>().timeScale;
            case SymbolKind::Package:
                return sym.as<PackageSymbol>().timeScale;
            default:
                if (sym.kind == SymbolKind::InstanceBody)
                    return sym.as<InstanceBodySymbol>().getDefinition().timeScale;
                else
                    current = sym.getParentScope();
                break;
        }
    } while (current);

    return getCompilation().getDefaultTimeScale();
}

VariableLifetime Scope::getDefaultLifetime() const {
    // If we're not in a procedural context, the default lifetime
    // is always just static (it's the only lifetime allowed).
    const Symbol* sym = &asSymbol();
    switch (sym->kind) {
        case SymbolKind::StatementBlock:
            return sym->as<StatementBlockSymbol>().defaultLifetime;
        case SymbolKind::Subroutine:
            return sym->as<SubroutineSymbol>().defaultLifetime;
        case SymbolKind::MethodPrototype:
            return VariableLifetime::Automatic;
        default:
            return VariableLifetime::Static;
    }
}

bool Scope::isProceduralContext() const {
    switch (asSymbol().kind) {
        case SymbolKind::ProceduralBlock:
        case SymbolKind::StatementBlock:
        case SymbolKind::Subroutine:
            return true;
        default:
            return false;
    }
}

Diagnostic& Scope::addDiag(DiagCode code, SourceLocation location) const {
    return compilation.addDiag(Diagnostic(*thisSym, code, location));
}

Diagnostic& Scope::addDiag(DiagCode code, SourceRange sourceRange) const {
    Diagnostic diag(*thisSym, code, sourceRange.start());
    diag << sourceRange;
    return compilation.addDiag(std::move(diag));
}

void Scope::addDiags(const Diagnostics& diags) const {
    for (auto& diag : diags) {
        Diagnostic copy = diag;
        copy.symbol = thisSym;
        compilation.addDiag(copy);
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
            LookupLocation ll(this, lastMember ? uint32_t(lastMember->getIndex()) + 1 : 1);
            compilation.createDefinition(*this, ll, syntax.as<ModuleDeclarationSyntax>());
            break;
        }
        case SyntaxKind::PackageDeclaration: {
            // Packages exist in their own namespace and are tracked in the Compilation.
            auto& package = compilation.createPackage(*this, syntax.as<ModuleDeclarationSyntax>());
            addMember(package);
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
                    import->setAttributes(*this, importDecl.attributes);
                    addMember(*import);
                }
            }
            break;
        }
        case SyntaxKind::HierarchyInstantiation:
        case SyntaxKind::AnsiPortList:
        case SyntaxKind::NonAnsiPortList:
        case SyntaxKind::IfGenerate:
        case SyntaxKind::CaseGenerate:
        case SyntaxKind::LoopGenerate:
        case SyntaxKind::GenerateBlock:
        case SyntaxKind::GateInstantiation:
        case SyntaxKind::ContinuousAssign:
        case SyntaxKind::ModportDeclaration:
        case SyntaxKind::UserDefinedNetDeclaration:
        case SyntaxKind::BindDirective: {
            auto sym = compilation.emplace<DeferredMemberSymbol>(syntax);
            addMember(*sym);
            getOrAddDeferredData().addMember(sym);
            break;
        }
        case SyntaxKind::PortDeclaration:
            getOrAddDeferredData().addPortDeclaration(syntax.as<PortDeclarationSyntax>(),
                                                      lastMember);
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration: {
            auto subroutine = SubroutineSymbol::fromSyntax(
                compilation, syntax.as<FunctionDeclarationSyntax>(), *this, /* outOfBlock */ false);
            if (subroutine)
                addMember(*subroutine);
            break;
        }
        case SyntaxKind::DataDeclaration: {
            // If this declaration has a named type, we need to defer the creation of the variables
            // because that type name may actually resolve to a net type or interface instance.
            auto& dataDecl = syntax.as<DataDeclarationSyntax>();
            if (dataDecl.type->kind == SyntaxKind::NamedType && dataDecl.modifiers.empty()) {
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
            NetSymbol::fromSyntax(*this, syntax.as<NetDeclarationSyntax>(), nets);
            for (auto net : nets)
                addMember(*net);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            SmallVectorSized<Symbol*, 8> params;
            ParameterSymbolBase::fromLocalSyntax(
                *this, syntax.as<ParameterDeclarationStatementSyntax>(), params);
            for (auto param : params)
                addMember(*param);
            break;
        }
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
            addMember(TypeAliasType::fromSyntax(*this, syntax.as<TypedefDeclarationSyntax>()));
            break;
        case SyntaxKind::ForwardTypedefDeclaration: {
            auto& symbol = ForwardingTypedefSymbol::fromSyntax(
                *this, syntax.as<ForwardTypedefDeclarationSyntax>());
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::ForwardInterfaceClassTypedefDeclaration: {
            auto& symbol = ForwardingTypedefSymbol::fromSyntax(
                *this, syntax.as<ForwardInterfaceClassTypedefDeclarationSyntax>());
            addMember(symbol);
            getOrAddDeferredData().addForwardingTypedef(symbol);
            break;
        }
        case SyntaxKind::GenerateRegion:
            for (auto member : syntax.as<GenerateRegionSyntax>().members)
                addMembers(*member);
            break;
        case SyntaxKind::NetTypeDeclaration:
            addMember(NetType::fromSyntax(*this, syntax.as<NetTypeDeclarationSyntax>()));
            break;
        case SyntaxKind::TimeUnitsDeclaration:
            // These are handled elsewhere; just ignore here.
            break;
        case SyntaxKind::GenvarDeclaration: {
            SmallVectorSized<const GenvarSymbol*, 16> genvars;
            GenvarSymbol::fromSyntax(*this, syntax.as<GenvarDeclarationSyntax>(), genvars);
            for (auto genvar : genvars)
                addMember(*genvar);
            break;
        }
        case SyntaxKind::ClassDeclaration:
            addMember(ClassType::fromSyntax(*this, syntax.as<ClassDeclarationSyntax>()));
            break;
        case SyntaxKind::ClassPropertyDeclaration: {
            auto& cpd = syntax.as<ClassPropertyDeclarationSyntax>();
            switch (cpd.declaration->kind) {
                case SyntaxKind::DataDeclaration: {
                    SmallVectorSized<const ClassPropertySymbol*, 4> symbols;
                    ClassPropertySymbol::fromSyntax(*this, cpd, symbols);
                    for (auto symbol : symbols)
                        addMember(*symbol);
                    break;
                }
                case SyntaxKind::TypedefDeclaration:
                    addMember(TypeAliasType::fromSyntax(*this, cpd));
                    break;
                case SyntaxKind::ForwardTypedefDeclaration:
                case SyntaxKind::ForwardInterfaceClassTypedefDeclaration: {
                    auto& symbol = ForwardingTypedefSymbol::fromSyntax(*this, cpd);
                    addMember(symbol);
                    getOrAddDeferredData().addForwardingTypedef(symbol);
                    break;
                }
                case SyntaxKind::ParameterDeclarationStatement: {
                    SmallVectorSized<Symbol*, 8> params;
                    ParameterSymbolBase::fromLocalSyntax(
                        *this, cpd.declaration->as<ParameterDeclarationStatementSyntax>(), params);
                    for (auto param : params)
                        addMember(*param);
                    break;
                }
                default:
                    // All other possible member kinds here are illegal and will
                    // be diagnosed in the parser, so just ignore them.
                    break;
            }
            break;
        }
        case SyntaxKind::ClassMethodDeclaration: {
            auto subroutine = SubroutineSymbol::fromSyntax(
                compilation, syntax.as<ClassMethodDeclarationSyntax>(), *this);
            if (subroutine)
                addMember(*subroutine);
            break;
        }
        case SyntaxKind::ClassMethodPrototype:
            addMember(
                MethodPrototypeSymbol::fromSyntax(*this, syntax.as<ClassMethodPrototypeSyntax>()));
            break;
        case SyntaxKind::ElabSystemTask:
            addMember(
                ElabSystemTaskSymbol::fromSyntax(compilation, syntax.as<ElabSystemTaskSyntax>()));
            break;
        case SyntaxKind::DPIImport:
            addMember(
                SubroutineSymbol::fromSyntax(compilation, syntax.as<DPIImportSyntax>(), *this));
            break;
        case SyntaxKind::DPIExport:
            compilation.noteDPIExportDirective(syntax.as<DPIExportSyntax>(), *this);
            break;
        case SyntaxKind::ConstraintDeclaration:
            if (auto sym = ConstraintBlockSymbol::fromSyntax(
                    *this, syntax.as<ConstraintDeclarationSyntax>())) {
                addMember(*sym);
            }
            break;
        case SyntaxKind::ConstraintPrototype:
            addMember(
                ConstraintBlockSymbol::fromSyntax(*this, syntax.as<ConstraintPrototypeSyntax>()));
            break;
        case SyntaxKind::DefParam: {
            SmallVectorSized<const DefParamSymbol*, 4> defparams;
            DefParamSymbol::fromSyntax(*this, syntax.as<DefParamSyntax>(), defparams);
            for (auto defparam : defparams)
                addMember(*defparam);
            break;
        }
        case SyntaxKind::ConcurrentAssertionMember:
        case SyntaxKind::ImmediateAssertionMember:
            // TODO: these aren't supported yet but we can compile everything else successfully
            // without them so warn instead of erroring.
            addDiag(diag::WarnNotYetSupported, syntax.sourceRange());
            break;
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
    while (symbol->kind == SymbolKind::TransparentMember)
        symbol = &symbol->as<TransparentMemberSymbol>().wrapped;

    switch (symbol->kind) {
        case SymbolKind::ExplicitImport:
        case SymbolKind::ForwardingTypedef:
            return nullptr;
        case SymbolKind::MethodPrototype:
            return symbol->as<MethodPrototypeSymbol>().getSubroutine();
        default:
            return symbol;
    }
}

const Symbol* Scope::lookupName(string_view name, LookupLocation location,
                                bitmask<LookupFlags> flags) const {
    LookupResult result;
    BindContext context(*this, location);
    Lookup::name(compilation.parseName(name), context, flags, result);
    ASSERT(result.selectors.empty());
    return result.found;
}

span<const WildcardImportSymbol* const> Scope::getWildcardImports() const {
    return compilation.queryImports(importDataIndex);
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

    // Add to the name map if the symbol has a name, unless it's a port.
    // Per the spec, ports exist in their own namespaces.
    if (!member->name.empty() && member->kind != SymbolKind::Port &&
        member->kind != SymbolKind::Package) {
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

    if (existing->kind == SymbolKind::ClassType && member.kind == SymbolKind::ForwardingTypedef) {
        // Class is already defined so nothing to do. When we elaborate the scope we will
        // check that the typedef had the correct 'class' specifier.
        existing->as<ClassType>().addForwardDecl(member.as<ForwardingTypedefSymbol>());
        return;
    }

    if (existing->kind == SymbolKind::GenericClassDef &&
        member.kind == SymbolKind::ForwardingTypedef) {
        // Class is already defined so nothing to do. When we elaborate the scope we will
        // check that the typedef had the correct 'class' specifier.
        existing->as<GenericClassDefSymbol>().addForwardDecl(member.as<ForwardingTypedefSymbol>());
        return;
    }

    if (existing->kind == SymbolKind::ForwardingTypedef) {
        if (member.kind == SymbolKind::ForwardingTypedef) {
            // Found another forwarding typedef; link it to the previous one.
            existing->as<ForwardingTypedefSymbol>().addForwardDecl(
                member.as<ForwardingTypedefSymbol>());
            return;
        }

        if (member.kind == SymbolKind::TypeAlias) {
            // We found the actual type for a previous forwarding declaration. Replace it in
            // the name map.
            member.as<TypeAliasType>().addForwardDecl(existing->as<ForwardingTypedefSymbol>());
            existing = &member;
            return;
        }

        if (member.kind == SymbolKind::ClassType) {
            member.as<ClassType>().addForwardDecl(existing->as<ForwardingTypedefSymbol>());
            existing = &member;
            return;
        }

        if (member.kind == SymbolKind::GenericClassDef) {
            member.as<GenericClassDefSymbol>().addForwardDecl(
                existing->as<ForwardingTypedefSymbol>());
            existing = &member;
            return;
        }
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

    // A formal argument (port) and its associated variable declaration get merged into one.
    // This is a pretty gross "feature" but oh well.
    if ((existing->kind == SymbolKind::FormalArgument || existing->kind == SymbolKind::Variable) &&
        (member.kind == SymbolKind::FormalArgument || member.kind == SymbolKind::Variable) &&
        member.kind != existing->kind) {

        // The lookup index should be whichever symbol is earlier.
        uint32_t index = std::min(uint32_t(existing->getIndex()), uint32_t(member.getIndex()));

        if (existing->kind == SymbolKind::FormalArgument) {
            if (const_cast<FormalArgumentSymbol&>(existing->as<FormalArgumentSymbol>())
                    .mergeVariable(member.as<VariableSymbol>())) {
                const_cast<Symbol*>(existing)->setIndex(SymbolIndex(index));
                return;
            }
        }
        else {
            if (const_cast<FormalArgumentSymbol&>(member.as<FormalArgumentSymbol>())
                    .mergeVariable(existing->as<VariableSymbol>())) {
                const_cast<Symbol*>(existing)->setIndex(SymbolIndex(index));
                existing = &member;
                return;
            }
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

    // If this is a class type being elaborated, let it inherit members from parent classes.
    if (thisSym->kind == SymbolKind::ClassType) {
        thisSym->as<ClassType>().inheritMembers(
            [this](const Symbol& member) { insertMember(&member, nullptr, true); });
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

    auto insertMembers = [this](auto& members, const Symbol* at) {
        for (auto member : members) {
            insertMember(member, at, true);
            at = member;
        }
    };

    // Go through deferred instances and elaborate them now. We skip generate blocks in
    // the initial pass because evaluating their conditions may depend on other members
    // that have yet to be elaborated. This implicitly implements the elaboration algorithm
    // described in [23.10.4.1].
    bool usedPorts = false;
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
                insertMembers(instances, symbol);
                break;
            }
            case SyntaxKind::GateInstantiation: {
                SmallVectorSized<const Symbol*, 8> instances;
                LookupLocation location = LookupLocation::before(*symbol);
                GateSymbol::fromSyntax(compilation, member.node.as<GateInstantiationSyntax>(),
                                       location, *this, instances);
                insertMembers(instances, symbol);
                break;
            }
            case SyntaxKind::AnsiPortList:
            case SyntaxKind::NonAnsiPortList: {
                SmallVectorSized<const Symbol*, 8> ports;
                SmallVectorSized<std::pair<Symbol*, const Symbol*>, 8> implicitMembers;
                PortSymbol::fromSyntax(member.node.as<PortListSyntax>(), *this, ports,
                                       implicitMembers, deferredData.getPortDeclarations());

                const Symbol* last = symbol;
                for (auto port : ports) {
                    insertMember(port, last, true);
                    last = port;
                }

                for (auto [implicitMember, insertionPoint] : implicitMembers)
                    insertMember(implicitMember, insertionPoint, true);

                // Let the instance know its list of ports. This is kind of annoying because it
                // inverts the dependency tree but it's better than giving all symbols a virtual
                // method just for this.
                asSymbol().as<InstanceBodySymbol>().setPorts(ports.copy(compilation));
                usedPorts = true;
                break;
            }
            case SyntaxKind::DataDeclaration: {
                SmallVectorSized<const ValueSymbol*, 4> symbols;
                VariableSymbol::fromSyntax(compilation, member.node.as<DataDeclarationSyntax>(),
                                           *this, symbols);
                insertMembers(symbols, symbol);
                break;
            }
            case SyntaxKind::ContinuousAssign: {
                SmallVectorSized<const Symbol*, 4> symbols;
                LookupLocation location = LookupLocation::before(*symbol);
                ContinuousAssignSymbol::fromSyntax(compilation,
                                                   member.node.as<ContinuousAssignSyntax>(), *this,
                                                   location, symbols);
                insertMembers(symbols, symbol);
                break;
            }
            case SyntaxKind::ModportDeclaration: {
                SmallVectorSized<const ModportSymbol*, 4> results;
                LookupLocation location = LookupLocation::before(*symbol);
                ModportSymbol::fromSyntax(*this, member.node.as<ModportDeclarationSyntax>(),
                                          location, results);
                insertMembers(results, symbol);
                break;
            }
            case SyntaxKind::BindDirective:
                InstanceSymbol::fromBindDirective(*this, member.node.as<BindDirectiveSyntax>());
                break;
            case SyntaxKind::UserDefinedNetDeclaration: {
                SmallVectorSized<const NetSymbol*, 4> results;
                LookupLocation location = LookupLocation::before(*symbol);
                NetSymbol::fromSyntax(*this, member.node.as<UserDefinedNetDeclarationSyntax>(),
                                      location, results);
                insertMembers(results, symbol);
                break;
            }
            default:
                break;
        }
    }

    // Issue an error if port I/Os were declared but the module doesn't have a port list.
    if (!usedPorts) {
        for (auto [syntax, symbol] : deferredData.getPortDeclarations()) {
            for (auto decl : syntax->declarators) {
                // We'll report an error for just the first decl in each syntax entry,
                // because it should be clear to the user that there aren't any ports
                // at all in the module header.
                auto name = decl->name.valueText();
                if (!name.empty()) {
                    addDiag(diag::UnusedPortDecl, decl->sourceRange()) << name;
                    break;
                }
            }
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
                constructIndex++;

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
                constructIndex++;

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
                constructIndex++;
                break;
            case SyntaxKind::GenerateBlock:
                // This case is invalid according to the spec but the parser only issues a warning
                // since some existing code does this anyway.
                insertMember(&GenerateBlockSymbol::fromSyntax(
                                 *this, member.node.as<GenerateBlockSyntax>(), constructIndex),
                             symbol, true);
                constructIndex++;
                break;
            default:
                break;
        }
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
        else if (it->second->kind == SymbolKind::ClassType)
            it->second->as<ClassType>().checkForwardDecls();
        else if (it->second->kind == SymbolKind::GenericClassDef)
            it->second->as<GenericClassDefSymbol>().checkForwardDecls();
        else
            addDiag(diag::UnresolvedForwardTypedef, symbol->location) << symbol->name;
    }

    // Allow statement blocks containing variables to include them in their member
    // list before allowing anyone else to access to the contained statements.
    if (thisSym->kind == SymbolKind::StatementBlock) {
        thisSym->as<StatementBlockSymbol>().elaborateVariables(
            [this](const Symbol& member) { insertMember(&member, nullptr, true); });
    }

    ASSERT(deferredMemberIndex == DeferredMemberIndex::Invalid);
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
    import->setAttributes(*this, attributes);
    addMember(*import);
    addWildcardImport(*import);
}

void Scope::addWildcardImport(const WildcardImportSymbol& item) {
    compilation.trackImport(importDataIndex, item);
}

void Scope::DeferredMemberData::addMember(Symbol* symbol) {
    members.emplace_back(symbol);
}

span<Symbol* const> Scope::DeferredMemberData::getMembers() const {
    return members;
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

void Scope::DeferredMemberData::addPortDeclaration(const PortDeclarationSyntax& syntax,
                                                   const Symbol* insertion) {
    portDecls.emplace_back(&syntax, insertion);
}

span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> Scope::DeferredMemberData::
    getPortDeclarations() const {
    return portDecls;
}

void Scope::DeferredMemberData::addNameConflict(const Symbol& member) {
    nameConflicts.push_back(&member);
}

span<const Symbol* const> Scope::DeferredMemberData::getNameConflicts() const {
    return nameConflicts;
}

} // namespace slang
