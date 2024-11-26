//------------------------------------------------------------------------------
// Scope.cpp
// Base class for symbols that represent lexical scopes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Scope.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SpecifySymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/TimeTrace.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::ast;

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

namespace slang::ast {

using namespace parsing;
using namespace syntax;

static size_t countMembers(const SyntaxNode& syntax);

Scope::Scope(Compilation& compilation_, const Symbol* thisSym_) :
    compilation(compilation_), thisSym(thisSym_), nameMap(compilation.allocSymbolMap()) {
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

std::optional<TimeScale> Scope::getTimeScale() const {
    const Scope* current = this;
    do {
        auto& sym = current->asSymbol();
        switch (sym.kind) {
            case SymbolKind::CompilationUnit:
                return sym.as<CompilationUnitSymbol>().timeScale;
            case SymbolKind::Package:
                return sym.as<PackageSymbol>().timeScale;
            case SymbolKind::InstanceBody:
                return sym.as<InstanceBodySymbol>().getDefinition().timeScale;
            default:
                current = sym.getParentScope();
                break;
        }
    } while (current);

    return getCompilation().getDefaultTimeScale();
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

const InstanceBodySymbol* Scope::getContainingInstance() const {
    auto currScope = this;
    while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
        currScope = currScope->asSymbol().getParentScope();

    if (currScope)
        return &currScope->asSymbol().as<InstanceBodySymbol>();

    return nullptr;
}

const CompilationUnitSymbol* Scope::getCompilationUnit() const {
    auto currScope = this;
    while (currScope && currScope->asSymbol().kind != SymbolKind::CompilationUnit)
        currScope = currScope->asSymbol().getParentScope();

    if (currScope)
        return &currScope->asSymbol().as<CompilationUnitSymbol>();

    return nullptr;
}

bool Scope::isUninstantiated() const {
    // In linting mode all contexts are considered uninstantiated.
    if (getCompilation().hasFlag(CompilationFlags::LintMode))
        return true;

    auto currScope = this;
    do {
        auto& sym = currScope->asSymbol();
        if (sym.kind == SymbolKind::InstanceBody)
            return sym.as<InstanceBodySymbol>().flags.has(InstanceFlags::Uninstantiated);
        if (sym.kind == SymbolKind::CheckerInstanceBody)
            return sym.as<CheckerInstanceBodySymbol>().flags.has(InstanceFlags::Uninstantiated);
        if (sym.kind == SymbolKind::GenerateBlock)
            return sym.as<GenerateBlockSymbol>().isUninstantiated;
        currScope = sym.getParentScope();
    } while (currScope);

    return false;
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

void Scope::addMembers(const SyntaxNode& syntax) {
    if (syntax.previewNode)
        addMembers(*syntax.previewNode);

    switch (syntax.kind) {
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration: {
            // Definitions exist in their own namespace and are tracked in the Compilation.
            LookupLocation ll(this, lastMember ? uint32_t(lastMember->getIndex()) + 1 : 1);
            compilation.createDefinition(*this, ll, syntax.as<ModuleDeclarationSyntax>());

            if (thisSym->kind != SymbolKind::Root && thisSym->kind != SymbolKind::CompilationUnit &&
                syntax.kind != SyntaxKind::InterfaceDeclaration) {
                addDeferredMembers(syntax);
            }
            break;
        }
        case SyntaxKind::PackageDeclaration: {
            // Packages exist in their own namespace and are tracked in the Compilation.
            auto& package = compilation.createPackage(*this, syntax.as<ModuleDeclarationSyntax>());
            addMember(package);
            break;
        }
        case SyntaxKind::UdpDeclaration:
            // Primitives exist in their own namespace and are tracked in the Compilation.
            compilation.createPrimitive(*this, syntax.as<UdpDeclarationSyntax>());
            break;
        case SyntaxKind::ConfigDeclaration:
            // Config blocks exist in their own namespace and are tracked in the Compilation.
            addMember(compilation.createConfigBlock(*this, syntax.as<ConfigDeclarationSyntax>()));
            break;
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
        case SyntaxKind::PackageExportDeclaration: {
            auto& exportDecl = syntax.as<PackageExportDeclarationSyntax>();
            for (auto item : exportDecl.items) {
                if (item->item.kind == TokenKind::Star) {
                    // These are handled manually as "wildcard imports" but don't get
                    // added to the import list. This is done just so that the package
                    // name itself gets validated and the attributes have somewhere to live.
                    // The actual export functionality is handled in PackageSymbol.
                    auto import = compilation.emplace<WildcardImportSymbol>(
                        item->package.valueText(), item->item.location());

                    import->setSyntax(*item);
                    import->setAttributes(*this, exportDecl.attributes);
                    import->isFromExport = true;
                    addMember(*import);
                }
                else {
                    auto import = compilation.emplace<ExplicitImportSymbol>(
                        item->package.valueText(), item->item.valueText(), item->item.location());

                    import->setSyntax(*item);
                    import->setAttributes(*this, exportDecl.attributes);
                    import->isFromExport = true;
                    addMember(*import);
                }
            }
            break;
        }
        case SyntaxKind::HierarchyInstantiation:
        case SyntaxKind::PrimitiveInstantiation:
        case SyntaxKind::CheckerInstantiation:
        case SyntaxKind::AnsiPortList:
        case SyntaxKind::NonAnsiPortList:
        case SyntaxKind::IfGenerate:
        case SyntaxKind::CaseGenerate:
        case SyntaxKind::LoopGenerate:
        case SyntaxKind::GenerateBlock:
        case SyntaxKind::ContinuousAssign:
        case SyntaxKind::ModportDeclaration:
        case SyntaxKind::ClockingItem:
        case SyntaxKind::DefaultClockingReference:
        case SyntaxKind::DefaultDisableDeclaration:
        case SyntaxKind::SpecifyBlock:
        case SyntaxKind::CoverCross:
        case SyntaxKind::NetAlias:
            addDeferredMembers(syntax);
            break;
        case SyntaxKind::EnumType:
            addDeferredMembers(syntax);
            getOrAddDeferredData().hasEnums = true;
            break;
        case SyntaxKind::PortDeclaration:
            addDeferredMembers(syntax);
            getOrAddDeferredData().addPortDeclaration(syntax, lastMember);
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration: {
            auto subroutine = SubroutineSymbol::fromSyntax(compilation,
                                                           syntax.as<FunctionDeclarationSyntax>(),
                                                           *this, /* outOfBlock */ false);
            if (subroutine)
                addMember(*subroutine);
            break;
        }
        case SyntaxKind::DataDeclaration: {
            // If this declaration has a named type we need to do a lookup here to see if it's
            // actually a user-defined nettype or a non-ansi interface port declaration.
            auto& dataDecl = syntax.as<DataDeclarationSyntax>();
            if (dataDecl.type->kind == SyntaxKind::NamedType && dataDecl.modifiers.empty()) {
                if (handleDataDeclaration(dataDecl))
                    break;
            }

            SmallVector<VariableSymbol*> symbols;
            VariableSymbol::fromSyntax(compilation, dataDecl, *this, /* isCheckerFreeVar */ false,
                                       symbols);
            for (auto symbol : symbols)
                addMember(*symbol);
            break;
        }
        case SyntaxKind::UserDefinedNetDeclaration:
            handleUserDefinedNet(syntax.as<UserDefinedNetDeclarationSyntax>());
            break;
        case SyntaxKind::NetDeclaration: {
            SmallVector<const NetSymbol*> nets;
            NetSymbol::fromSyntax(*this, syntax.as<NetDeclarationSyntax>(), nets);
            for (auto net : nets)
                addMember(*net);
            break;
        }
        case SyntaxKind::CheckerDataDeclaration: {
            SmallVector<VariableSymbol*> symbols;
            VariableSymbol::fromSyntax(compilation, *syntax.as<CheckerDataDeclarationSyntax>().data,
                                       *this, /* isCheckerFreeVar */ true, symbols);
            for (auto symbol : symbols)
                addMember(*symbol);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            SmallVector<Symbol*> params;
            ParameterSymbolBase::fromLocalSyntax(*this,
                                                 syntax.as<ParameterDeclarationStatementSyntax>(),
                                                 params);
            for (auto param : params)
                addMember(*param);
            break;
        }
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysLatchBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock:
            addMember(ProceduralBlockSymbol::fromSyntax(*this, syntax.as<ProceduralBlockSyntax>()));
            break;
        case SyntaxKind::ConcurrentAssertionMember:
            addMember(ProceduralBlockSymbol::fromSyntax(
                *this, syntax.as<ConcurrentAssertionMemberSyntax>()));
            break;
        case SyntaxKind::ImmediateAssertionMember:
            addMember(ProceduralBlockSymbol::fromSyntax(
                *this, syntax.as<ImmediateAssertionMemberSyntax>()));
            break;
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
        case SyntaxKind::GenerateRegion:
            for (auto member : syntax.as<GenerateRegionSyntax>().members)
                addMembers(*member);
            break;
        case SyntaxKind::NetTypeDeclaration:
            addMember(NetType::fromSyntax(*this, syntax.as<NetTypeDeclarationSyntax>()));
            break;
        case SyntaxKind::TimeUnitsDeclaration:
        case SyntaxKind::PackageExportAllDeclaration:
            // These are handled elsewhere; just ignore here.
            break;
        case SyntaxKind::GenvarDeclaration: {
            SmallVector<const GenvarSymbol*> genvars;
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
                    SmallVector<const ClassPropertySymbol*> symbols;
                    ClassPropertySymbol::fromSyntax(*this, cpd, symbols);
                    for (auto symbol : symbols)
                        addMember(*symbol);
                    break;
                }
                case SyntaxKind::TypedefDeclaration:
                    addMember(TypeAliasType::fromSyntax(*this, cpd));
                    break;
                case SyntaxKind::ForwardTypedefDeclaration: {
                    auto& symbol = ForwardingTypedefSymbol::fromSyntax(*this, cpd);
                    addMember(symbol);
                    getOrAddDeferredData().addForwardingTypedef(symbol);
                    break;
                }
                case SyntaxKind::ParameterDeclarationStatement: {
                    SmallVector<Symbol*> params;
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
            // Constructors need to be deferred because they may need to
            // inherit arguments from their base class.
            auto& cmds = syntax.as<ClassMethodDeclarationSyntax>();
            if (cmds.declaration->prototype->name->getLastToken().kind == TokenKind::NewKeyword)
                addDeferredMembers(syntax);
            else if (auto subroutine = SubroutineSymbol::fromSyntax(compilation, cmds, *this))
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
        case SyntaxKind::BindDirective:
            compilation.noteBindDirective(syntax.as<BindDirectiveSyntax>(), *this);
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
            SmallVector<const DefParamSymbol*> defparams;
            DefParamSymbol::fromSyntax(*this, syntax.as<DefParamSyntax>(), defparams);
            for (auto defparam : defparams)
                addMember(*defparam);
            break;
        }
        case SyntaxKind::SpecparamDeclaration: {
            SmallVector<const SpecparamSymbol*> params;
            SpecparamSymbol::fromSyntax(*this, syntax.as<SpecparamDeclarationSyntax>(), params);
            for (auto param : params)
                addMember(*param);
            break;
        }
        case SyntaxKind::SequenceDeclaration:
            addMember(SequenceSymbol::fromSyntax(*this, syntax.as<SequenceDeclarationSyntax>()));
            break;
        case SyntaxKind::PropertyDeclaration:
            addMember(PropertySymbol::fromSyntax(*this, syntax.as<PropertyDeclarationSyntax>()));
            break;
        case SyntaxKind::ClockingDeclaration:
            addMember(
                ClockingBlockSymbol::fromSyntax(*this, syntax.as<ClockingDeclarationSyntax>()));
            break;
        case SyntaxKind::LetDeclaration:
            addMember(LetDeclSymbol::fromSyntax(*this, syntax.as<LetDeclarationSyntax>()));
            break;
        case SyntaxKind::CheckerDeclaration:
            addMember(CheckerSymbol::fromSyntax(*this, syntax.as<CheckerDeclarationSyntax>()));
            break;
        case SyntaxKind::CovergroupDeclaration: {
            const Symbol* classProperty = nullptr;
            addMember(CovergroupType::fromSyntax(*this, syntax.as<CovergroupDeclarationSyntax>(),
                                                 classProperty));
            if (classProperty)
                addMember(*classProperty);
            break;
        }
        case SyntaxKind::Coverpoint:
            addMember(CoverpointSymbol::fromSyntax(*this, syntax.as<CoverpointSyntax>()));
            break;
        case SyntaxKind::CoverageBins:
            addMember(CoverageBinSymbol::fromSyntax(*this, syntax.as<CoverageBinsSyntax>()));
            break;
        case SyntaxKind::BinsSelection:
            addMember(CoverageBinSymbol::fromSyntax(*this, syntax.as<BinsSelectionSyntax>()));
            break;
        case SyntaxKind::ExternInterfaceMethod:
            addMember(
                MethodPrototypeSymbol::fromSyntax(*this, syntax.as<ExternInterfaceMethodSyntax>()));
            break;
        case SyntaxKind::PathDeclaration:
            addMember(TimingPathSymbol::fromSyntax(*this, syntax.as<PathDeclarationSyntax>()));
            break;
        case SyntaxKind::IfNonePathDeclaration:
            addMember(
                TimingPathSymbol::fromSyntax(*this, syntax.as<IfNonePathDeclarationSyntax>()));
            break;
        case SyntaxKind::ConditionalPathDeclaration:
            addMember(
                TimingPathSymbol::fromSyntax(*this, syntax.as<ConditionalPathDeclarationSyntax>()));
            break;
        case SyntaxKind::PulseStyleDeclaration:
            addMember(
                PulseStyleSymbol::fromSyntax(*this, syntax.as<PulseStyleDeclarationSyntax>()));
            break;
        case SyntaxKind::SystemTimingCheck:
            addMember(
                SystemTimingCheckSymbol::fromSyntax(*this, syntax.as<SystemTimingCheckSyntax>()));
            break;
        case SyntaxKind::AnonymousProgram:
            addMember(
                AnonymousProgramSymbol::fromSyntax(*this, syntax.as<AnonymousProgramSyntax>()));
            break;
        case SyntaxKind::ExternModuleDecl:
        case SyntaxKind::ExternUdpDecl:
            compilation.noteExternDefinition(*this, syntax);
            break;
        case SyntaxKind::WildcardPortList:
            // If we hit this case we've run into an error elsewhere.
            // Just silently ignore it here.
            break;
        case SyntaxKind::LibraryDeclaration:
        case SyntaxKind::LibraryIncludeStatement:
            // These are ignored here, they're only processed during
            // library map construction.
            break;
        default:
            SLANG_UNREACHABLE;
    }
}

const Symbol* Scope::find(std::string_view name) const {
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
        case SymbolKind::ModportClocking:
            return symbol->as<ModportClockingSymbol>().target;
        default:
            return symbol;
    }
}

const Symbol* Scope::lookupName(std::string_view name, LookupLocation location,
                                bitmask<LookupFlags> flags) const {
    LookupResult result;
    ASTContext context(*this, location);
    Lookup::name(compilation.parseName(name), context, flags, result);
    SLANG_ASSERT(result.selectors.empty());
    return result.found;
}

Scope::DeferredMemberData& Scope::getOrAddDeferredData() const {
    return compilation.getOrAddDeferredData(deferredMemberIndex);
}

void Scope::addDeferredMembers(const SyntaxNode& syntax) {
    auto sym = compilation.emplace<DeferredMemberSymbol>(syntax);
    addMember(*sym);
    getOrAddDeferredData().addMember(sym);

    // We need to figure out how many new symbols could be inserted when we
    // later elaborate this deferred member, so that we can make room in the
    // index space such that no symbols need to overlap.
    sym->indexInScope += (uint32_t)countMembers(syntax);
}

static bool canLookupByName(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Port:
        case SymbolKind::MultiPort:
        case SymbolKind::Package:
        case SymbolKind::Primitive:
        case SymbolKind::ConfigBlock:
            return false;
        default:
            return true;
    }
}

void Scope::insertMember(const Symbol* member, const Symbol* at, bool isElaborating,
                         bool incrementIndex) const {
    SLANG_ASSERT(!member->parentScope);
    SLANG_ASSERT(!member->nextInScope);

    if (!at) {
        member->indexInScope = SymbolIndex{1};
        member->nextInScope = std::exchange(firstMember, member);
    }
    else {
        member->indexInScope = at->indexInScope + (incrementIndex ? 1 : 0);
        member->nextInScope = std::exchange(at->nextInScope, member);
    }

    member->parentScope = this;
    if (!member->nextInScope)
        lastMember = member;

    // Add to the name map if the symbol has a name and can be looked up
    // by name in the default namespace.
    if (!member->name.empty() && canLookupByName(member->kind)) {
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

    if (existing->kind == SymbolKind::ExplicitImport && member.kind == SymbolKind::ExplicitImport) {
        if (!isElaborating) {
            // These can't be checked until we can resolve the imports and
            // see if they point to the same symbol.
            compilation.noteNameConflict(member);
        }
        else {
            checkImportConflict(member, *existing);
        }
        return;
    }

    if (existing->kind == SymbolKind::GenerateBlock && member.kind == SymbolKind::GenerateBlock) {
        // If both are generate blocks and both are from the same generate construct, it's ok
        // for them to have the same name. We take the one that is instantiated.
        auto& gen1 = existing->as<GenerateBlockSymbol>();
        auto& gen2 = member.as<GenerateBlockSymbol>();
        if (gen1.constructIndex == gen2.constructIndex) {
            SLANG_ASSERT(gen1.isUninstantiated || gen2.isUninstantiated);
            if (gen1.isUninstantiated)
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
        compilation.noteNameConflict(member);
        return;
    }

    reportNameConflict(member, *existing);
}

void Scope::handleNameConflict(const Symbol& member) const {
    auto existing = nameMap->find(member.name)->second;
    SLANG_ASSERT(existing);
    if (member.kind == SymbolKind::ExplicitImport)
        checkImportConflict(member, *existing);
    else
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
    else {
        diag = &addDiag(diag::Redefinition, member.location);
        (*diag) << member.name;
    }
    diag->addNote(diag::NotePreviousDefinition, existing.location);
}

void Scope::checkImportConflict(const Symbol& member, const Symbol& existing) const {
    auto& mei = member.as<ExplicitImportSymbol>();
    auto& eei = existing.as<ExplicitImportSymbol>();

    auto s1 = mei.importedSymbol();
    auto s2 = eei.importedSymbol();
    if (!s1 || !s2)
        return;

    if (s1 == s2) {
        if (!mei.isFromExport && !eei.isFromExport) {
            // Duplicate explicit imports are specifically allowed,
            // so just ignore the other one (with a warning).
            auto& diag = addDiag(diag::DuplicateImport, member.location);
            diag.addNote(diag::NotePreviousDefinition, existing.location);
        }
    }
    else {
        reportNameConflict(member, existing);
    }
}

void Scope::elaborate() const {
    if (thisSym->kind == SymbolKind::InstanceBody && TimeTrace::isEnabled()) {
        TimeTrace::beginTrace("elaborate scope"sv, [&] {
            std::string buffer;
            thisSym->getHierarchicalPath(buffer);
            return buffer;
        });
    }

    SLANG_ASSERT(deferredMemberIndex != DeferredMemberIndex::Invalid);
    auto deferredData = compilation.getOrAddDeferredData(deferredMemberIndex);
    auto deferred = deferredData.getMembers();
    deferredMemberIndex = DeferredMemberIndex::Invalid;

    // Enums need to be handled first because their value members may need
    // to be looked up by methods below.
    if (deferredData.hasEnums) {
        for (auto symbol : deferred) {
            const Symbol* at = symbol;
            auto& node = symbol->as<DeferredMemberSymbol>().node;
            if (node.kind == SyntaxKind::EnumType) {
                ASTContext context(*this, LookupLocation::before(*symbol));
                EnumType::fromSyntax(compilation, node.as<EnumTypeSyntax>(), context,
                                     [this, &at](const Symbol& member) {
                                         auto wrapped =
                                             compilation.emplace<TransparentMemberSymbol>(member);
                                         insertMember(wrapped, at, true, false);
                                         at = wrapped;
                                     });
            }
        }
    }

    if (thisSym->kind == SymbolKind::ClassType) {
        // If this is a class type being elaborated, let it inherit members from parent classes.
        thisSym->as<ClassType>().inheritMembers(
            [this](const Symbol& member) { insertMember(&member, nullptr, true, true); });
    }
    else if (thisSym->kind == SymbolKind::CovergroupType) {
        // If this is a covergroup type being elaborated, let it inherit members from parent
        // classes.
        thisSym->as<CovergroupType>().inheritMembers(
            [this](const Symbol& member) { insertMember(&member, nullptr, true, true); });
    }
    else if (thisSym->kind == SymbolKind::InstanceBody &&
             thisSym->as<InstanceBodySymbol>().getDefinition().definitionKind ==
                 DefinitionKind::Interface) {
        // Allow the interface to implicitly declare extern methods for
        // exported subroutines that are only declared in modports.
        handleExportedMethods(deferred);
    }

    auto insertMembers = [this](auto& members, const Symbol* at) {
        // When we originally inserted the DeferredMemberSymbol we made room
        // in the index space for these new members. Back the index up by
        // the number of new members to make sure we insert in order.
        SLANG_ASSERT(at);
        at->indexInScope -= (uint32_t)members.size();
        for (auto member : members) {
            insertMember(member, at, true, true);
            at = member;
        }
    };

    auto insertMembersAndNets = [this](auto& members, auto& implicitNets, const Symbol* at) {
        SLANG_ASSERT(at);
        at->indexInScope -= (uint32_t)members.size() + 1;
        for (auto net : implicitNets) {
            insertMember(net, at, true, false);
            at = net;
        }

        at->indexInScope += 1;
        for (auto member : members) {
            insertMember(member, at, true, true);
            at = member;
        }
    };

    // Go through deferred instances and elaborate them now.
    bool usedPorts = false;
    bool hasNestedDefs = false;
    bool hasBinds = false;
    uint32_t constructIndex = 1;

    for (auto symbol : deferred) {
        ASTContext context(*this, LookupLocation::before(*symbol));
        auto& member = symbol->as<DeferredMemberSymbol>();

        switch (member.node.kind) {
            case SyntaxKind::HierarchyInstantiation: {
                SmallVector<const Symbol*> instances;
                SmallVector<const Symbol*> implicitNets;
                InstanceSymbol::fromSyntax(compilation,
                                           member.node.as<HierarchyInstantiationSyntax>(), context,
                                           instances, implicitNets);
                insertMembersAndNets(instances, implicitNets, symbol);
                break;
            }
            case SyntaxKind::PrimitiveInstantiation: {
                SmallVector<const Symbol*> instances;
                SmallVector<const Symbol*> implicitNets;
                PrimitiveInstanceSymbol::fromSyntax(member.node.as<PrimitiveInstantiationSyntax>(),
                                                    context, instances, implicitNets);
                insertMembersAndNets(instances, implicitNets, symbol);
                break;
            }
            case SyntaxKind::CheckerInstantiation: {
                SmallVector<const Symbol*> instances;
                SmallVector<const Symbol*> implicitNets;
                CheckerInstanceSymbol::fromSyntax(member.node.as<CheckerInstantiationSyntax>(),
                                                  context, instances, implicitNets,
                                                  InstanceFlags::None);
                insertMembersAndNets(instances, implicitNets, symbol);
                break;
            }
            case SyntaxKind::IfGenerate: {
                SmallVector<GenerateBlockSymbol*> blocks;
                GenerateBlockSymbol::fromSyntax(compilation, member.node.as<IfGenerateSyntax>(),
                                                context, constructIndex, isUninstantiated(),
                                                blocks);
                constructIndex++;
                insertMembers(blocks, symbol);
                break;
            }
            case SyntaxKind::CaseGenerate: {
                SmallVector<GenerateBlockSymbol*> blocks;
                GenerateBlockSymbol::fromSyntax(compilation, member.node.as<CaseGenerateSyntax>(),
                                                context, constructIndex, isUninstantiated(),
                                                blocks);
                constructIndex++;
                insertMembers(blocks, symbol);
                break;
            }
            case SyntaxKind::LoopGenerate:
                insertMember(&GenerateBlockArraySymbol::fromSyntax(
                                 compilation, member.node.as<LoopGenerateSyntax>(),
                                 symbol->getIndex(), context, constructIndex),
                             symbol, true, true);
                constructIndex++;
                break;
            case SyntaxKind::GenerateBlock:
                // This case is invalid according to the spec but the parser only issues a warning
                // since some existing code does this anyway.
                insertMember(&GenerateBlockSymbol::fromSyntax(
                                 *this, member.node.as<GenerateBlockSyntax>(), constructIndex),
                             symbol, true, true);
                constructIndex++;
                break;
            case SyntaxKind::AnsiPortList:
            case SyntaxKind::NonAnsiPortList: {
                SmallVector<const Symbol*> ports;
                SmallVector<std::pair<Symbol*, const Symbol*>, 4> implicitMembers;
                PortSymbol::fromSyntax(member.node.as<PortListSyntax>(), *this, ports,
                                       implicitMembers, deferredData.getPortDeclarations());
                insertMembers(ports, symbol);

                for (auto [implicitMember, insertionPoint] : implicitMembers)
                    insertMember(implicitMember, insertionPoint, true, false);

                // Let the instance know its list of ports. This is kind of annoying because it
                // inverts the dependency tree but it's better than giving all symbols a virtual
                // method just for this.
                asSymbol().as<InstanceBodySymbol>().setPorts(ports.copy(compilation));
                usedPorts = true;
                break;
            }
            case SyntaxKind::ContinuousAssign: {
                SmallVector<const Symbol*> symbols;
                SmallVector<const Symbol*> implicitNets;
                ContinuousAssignSymbol::fromSyntax(compilation,
                                                   member.node.as<ContinuousAssignSyntax>(),
                                                   context, symbols, implicitNets);
                insertMembersAndNets(symbols, implicitNets, symbol);
                break;
            }
            case SyntaxKind::ModportDeclaration: {
                SmallVector<const ModportSymbol*> results;
                ModportSymbol::fromSyntax(context, member.node.as<ModportDeclarationSyntax>(),
                                          results);
                insertMembers(results, symbol);
                break;
            }
            case SyntaxKind::ClockingItem: {
                SmallVector<const ClockVarSymbol*> vars;
                ClockVarSymbol::fromSyntax(*this, member.node.as<ClockingItemSyntax>(), vars);
                insertMembers(vars, symbol);
                break;
            }
            case SyntaxKind::DefaultClockingReference: {
                // No symbol to create here; instead, try to look up the clocking block
                // and register it as a default.
                compilation.noteDefaultClocking(context,
                                                member.node.as<DefaultClockingReferenceSyntax>());
                break;
            }
            case SyntaxKind::DefaultDisableDeclaration: {
                // No symbol to create here; instead, bind the expression and hand it
                // off to the compilation for tracking.
                auto& expr = Expression::bind(
                    *member.node.as<DefaultDisableDeclarationSyntax>().expr, context);

                if (!expr.bad()) {
                    if (!expr.type->isVoid())
                        context.requireBooleanConvertible(expr);

                    compilation.noteDefaultDisable(*this, expr);
                }
                break;
            }
            case SyntaxKind::PortDeclaration:
                // Nothing to do here, handled by port creation.
                break;
            case SyntaxKind::DataDeclaration: {
                SmallVector<const Symbol*> instances;
                tryFixupInstances(member.node.as<DataDeclarationSyntax>(), context, instances);
                insertMembers(instances, symbol);
                break;
            }
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::ProgramDeclaration:
                // These have to wait until we've seen all instantiations.
                hasNestedDefs = true;
                break;
            case SyntaxKind::SpecifyBlock: {
                SmallVector<const Symbol*> implicitSymbols;
                auto& specify = SpecifyBlockSymbol::fromSyntax(*this,
                                                               member.node.as<SpecifyBlockSyntax>(),
                                                               implicitSymbols);

                auto members = {&specify};
                insertMembersAndNets(members, implicitSymbols, symbol);
                break;
            }
            case SyntaxKind::CoverCross: {
                SmallVector<const Symbol*> implicitMembers;
                auto& cross = CoverCrossSymbol::fromSyntax(*this,
                                                           member.node.as<CoverCrossSyntax>(),
                                                           implicitMembers);
                auto members = {&cross};
                insertMembersAndNets(members, implicitMembers, symbol);
                cross.addBody(member.node.as<CoverCrossSyntax>(), *this);
                break;
            }
            case SyntaxKind::NetAlias: {
                SmallVector<const Symbol*> implicitNets;
                auto& alias = NetAliasSymbol::fromSyntax(context, member.node.as<NetAliasSyntax>(),
                                                         implicitNets);
                auto members = {&alias};
                insertMembersAndNets(members, implicitNets, symbol);
                break;
            }
            case SyntaxKind::BindDirective: {
                // Process bind directives below after everything else.
                hasBinds = true;
                break;
            }
            case SyntaxKind::ClassMethodDeclaration: {
                auto subroutine = SubroutineSymbol::fromSyntax(
                    compilation, member.node.as<ClassMethodDeclarationSyntax>(), *this);
                if (subroutine)
                    insertMember(subroutine, symbol, true, true);
                break;
            }
            case SyntaxKind::EnumType:
                // Already handled above.
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    // If there are nested definitions, go back through and find ones that
    // need to be implicitly instantiated.
    if (hasNestedDefs) {
        for (auto symbol : deferred) {
            auto& member = symbol->as<DeferredMemberSymbol>();
            if (member.node.kind == SyntaxKind::ModuleDeclaration ||
                member.node.kind == SyntaxKind::ProgramDeclaration) {
                handleNestedDefinition(member.node.as<ModuleDeclarationSyntax>());
            }
        }
    }

    if (usedPorts) {
        // Now that all members are known, force port types to resolve so that
        // back references to internal variables and nets are known.
        for (auto port : asSymbol().as<InstanceBodySymbol>().portList) {
            switch (port->kind) {
                case SymbolKind::Port:
                    port->as<PortSymbol>().getType();
                    break;
                case SymbolKind::MultiPort:
                    port->as<MultiPortSymbol>().getType();
                    break;
                default:
                    break;
            }
        }
    }
    else {
        // Issue an error if port I/Os were declared but the module doesn't have a port list.
        for (auto [syntax, symbol] : deferredData.getPortDeclarations()) {
            auto& declarators = syntax->kind == SyntaxKind::PortDeclaration
                                    ? syntax->as<PortDeclarationSyntax>().declarators
                                    : syntax->as<DataDeclarationSyntax>().declarators;
            for (auto decl : declarators) {
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

    // If there are bind directives, reach up into the instance body
    // and pull out the extra bind metadata from its override node.
    if (hasBinds) {
        SmallSet<const BindDirectiveSyntax*, 4> seenBindDirectives;
        ASTContext context(*this, LookupLocation::max);
        auto handleBind = [&](const BindDirectiveInfo& info) {
            if (!seenBindDirectives.emplace(info.bindSyntax).second) {
                addDiag(diag::DuplicateBind, info.bindSyntax->sourceRange());
                return;
            }

            SmallVector<const Symbol*> instances;
            SmallVector<const Symbol*> implicitNets;
            if (info.bindSyntax->instantiation->kind == SyntaxKind::CheckerInstantiation) {
                CheckerInstanceSymbol::fromSyntax(
                    info.bindSyntax->instantiation->as<CheckerInstantiationSyntax>(), context,
                    instances, implicitNets, InstanceFlags::FromBind);
            }
            else {
                InstanceSymbol::fromSyntax(
                    compilation, info.bindSyntax->instantiation->as<HierarchyInstantiationSyntax>(),
                    context, instances, implicitNets, &info);
            }

            for (auto sym : implicitNets)
                insertMember(sym, lastMember, true, false);
            for (auto sym : instances)
                insertMember(sym, lastMember, true, true);
        };

        auto& instanceBody = asSymbol().as<InstanceBodySymbol>();
        if (auto node = instanceBody.hierarchyOverrideNode) {
            for (auto& [bindInfo, targetDefSyntax] : node->binds) {
                if (!targetDefSyntax)
                    handleBind(bindInfo);
            }
        }

        if (!instanceBody.getDefinition().bindDirectives.empty()) {
            for (auto& bindInfo : instanceBody.getDefinition().bindDirectives)
                handleBind(bindInfo);
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

    SmallSet<std::string_view, 4> observedForwardDecls;
    for (auto symbol : deferredData.getForwardingTypedefs()) {
        // Ignore duplicate entries.
        if (symbol->name.empty() || !observedForwardDecls.emplace(symbol->name).second)
            continue;

        // Try to do a lookup by name; if the program is well-formed we'll find the
        // corresponding full typedef. If we don't, issue an error.
        auto it = nameMap->find(symbol->name);
        SLANG_ASSERT(it != nameMap->end());

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
    // list before allowing anyone else to access the contained statements.
    if (thisSym->kind == SymbolKind::StatementBlock) {
        const Symbol* at = nullptr;
        thisSym->as<StatementBlockSymbol>().elaborateVariables([this, &at](const Symbol& member) {
            insertMember(&member, at, true, false);
            at = &member;
        });
    }

    SLANG_ASSERT(deferredMemberIndex == DeferredMemberIndex::Invalid);
    if (thisSym->kind == SymbolKind::InstanceBody && TimeTrace::isEnabled())
        TimeTrace::endTrace();
}

static std::string_view getIdentifierName(const NamedTypeSyntax& syntax) {
    if (syntax.name->kind == SyntaxKind::IdentifierName)
        return syntax.name->as<IdentifierNameSyntax>().identifier.valueText();

    if (syntax.name->kind == SyntaxKind::ClassName)
        return syntax.name->as<ClassNameSyntax>().identifier.valueText();

    return ""sv;
}

bool Scope::handleDataDeclaration(const DataDeclarationSyntax& syntax) {
    auto& namedType = syntax.type->as<NamedTypeSyntax>();
    std::string_view name = getIdentifierName(namedType);
    if (name.empty())
        return false;

    // We aren't elaborated yet so can't do a normal lookup in this scope.
    // Temporarily swap out the deferred member index so that the lookup
    // doesn't trigger elaboration.
    auto savedIndex = std::exchange(deferredMemberIndex, DeferredMemberIndex::Invalid);
    auto symbol = Lookup::unqualified(*this, name);
    deferredMemberIndex = savedIndex;

    // If we found a net type, this is actually one or more net symbols.
    if (symbol && symbol->kind == SymbolKind::NetType) {
        auto& netType = symbol->as<NetType>();
        for (auto decl : syntax.declarators) {
            auto net = compilation.emplace<NetSymbol>(decl->name.valueText(), decl->name.location(),
                                                      netType);
            net->setFromDeclarator(*decl);
            net->setAttributes(*this, syntax.attributes);
            addMember(*net);
        }

        // Make sure we're not declared within a checker.
        const Scope* currScope = this;
        do {
            auto& sym = currScope->asSymbol();
            if (sym.kind == SymbolKind::InstanceBody)
                break;

            if (sym.kind == SymbolKind::CheckerInstanceBody) {
                addDiag(diag::NotAllowedInChecker, syntax.sourceRange());
                break;
            }

            currScope = sym.getParentScope();
        } while (currScope);

        return true;
    }

    // No user-defined net type found. If this is a simple name and no symbol at all
    // was found we should continue on to see if this is a non-ansi interface port.
    if (symbol || namedType.name->kind != SyntaxKind::IdentifierName)
        return false;

    auto def = compilation.tryGetDefinition(name, *this).definition;
    if (!def || def->kind != SymbolKind::Definition)
        return false;

    // If we're in an instance and have non-ansi ports then assume that this is
    // a non-ansi interface port definition.
    if (def->as<DefinitionSymbol>().definitionKind == DefinitionKind::Interface &&
        asSymbol().kind == SymbolKind::InstanceBody &&
        asSymbol().as<InstanceBodySymbol>().getDefinition().hasNonAnsiPorts) {

        // Save for later when we process the ports.
        addDeferredMembers(syntax);
        getOrAddDeferredData().addPortDeclaration(syntax, lastMember);
        return true;
    }

    // If we made it this far it's probably a malformed instantiation -- the user forgot
    // to include the parentheses. Let's just treat it like an instantiation instead, as
    // long as there are no decl initializers (which would never look like an instantiation).
    for (auto decl : syntax.declarators) {
        if (decl->initializer)
            return false;
    }

    addDeferredMembers(syntax);
    return true;
}

void Scope::tryFixupInstances(const DataDeclarationSyntax& syntax, const ASTContext& context,
                              SmallVectorBase<const Symbol*>& results) const {
    auto& namedType = syntax.type->as<NamedTypeSyntax>();
    std::string_view name = getIdentifierName(namedType);
    auto def = compilation.tryGetDefinition(name, *this).definition;
    if (!def || def->kind != SymbolKind::Definition)
        return;

    // Matching the check in handleDataDeclaration -- if this is true we
    // handle this as a non-ansi interface port declaration instead.
    auto& defSym = def->as<DefinitionSymbol>();
    if (defSym.definitionKind == DefinitionKind::Interface &&
        asSymbol().kind == SymbolKind::InstanceBody &&
        asSymbol().as<InstanceBodySymbol>().getDefinition().hasNonAnsiPorts) {
        return;
    }

    // Assume this is malformed instantiation syntax and create the instances anyway.
    InstanceSymbol::fromFixupSyntax(compilation, defSym, syntax, context, results);
}

void Scope::handleUserDefinedNet(const UserDefinedNetDeclarationSyntax& syntax) {
    // We aren't elaborated yet so can't do a normal lookup in this scope.
    // Temporarily swap out the deferred member index so that the lookup
    // doesn't trigger elaboration.
    auto savedIndex = std::exchange(deferredMemberIndex, DeferredMemberIndex::Invalid);
    auto symbol = Lookup::unqualifiedAt(*this, syntax.netType.valueText(), LookupLocation::max,
                                        syntax.netType.range());
    deferredMemberIndex = savedIndex;

    SmallVector<const NetSymbol*> results;
    NetSymbol::fromSyntax(*this, syntax, symbol, results);
    for (auto sym : results)
        addMember(*sym);
}

void Scope::handleNestedDefinition(const ModuleDeclarationSyntax& syntax) const {
    // We implicitly instantiate this definition if it has no parameters
    // and no ports and hasn't been instantiated elsewhere.
    auto& header = *syntax.header;
    if (header.parameters && !header.parameters->declarations.empty())
        return;

    if (header.ports) {
        if (header.ports->kind == SyntaxKind::AnsiPortList) {
            if (!header.ports->as<AnsiPortListSyntax>().ports.empty())
                return;
        }
        else if (header.ports->kind == SyntaxKind::NonAnsiPortList) {
            if (!header.ports->as<NonAnsiPortListSyntax>().ports.empty())
                return;
        }
        else {
            return;
        }
    }

    auto def = compilation.getDefinition(*this, syntax);
    if (!def || def->getInstanceCount() > 0)
        return;

    auto& inst = InstanceSymbol::createDefaultNested(*this, syntax);
    insertMember(&inst, lastMember, /* isElaborating */ true, /* incrementIndex */ true);
}

void Scope::handleExportedMethods(std::span<Symbol* const> deferredMembers) const {
    SmallSet<std::string_view, 4> waitingForImport;
    SmallMap<std::string_view, const ModportSubroutinePortSyntax*, 4> foundImports;

    auto create = [&](const ModportSubroutinePortSyntax& syntax) {
        auto& symbol = MethodPrototypeSymbol::implicitExtern(*this, syntax);
        insertMember(&symbol, nullptr, true, true);
    };

    for (auto symbol : deferredMembers) {
        auto& node = symbol->as<DeferredMemberSymbol>().node;
        if (node.kind != SyntaxKind::ModportDeclaration)
            continue;

        for (auto item : node.as<ModportDeclarationSyntax>().items) {
            for (auto port : item->ports->ports) {
                if (port->kind != SyntaxKind::ModportSubroutinePortList)
                    continue;

                auto& portList = port->as<ModportSubroutinePortListSyntax>();
                bool isExport = portList.importExport.kind == TokenKind::ExportKeyword;

                for (auto subPort : portList.ports) {
                    switch (subPort->kind) {
                        case SyntaxKind::ModportNamedPort: {
                            // A simple named export is not enough to create a
                            // new extern prototype, but if an import has already
                            // declared it for us then we can take details from that.
                            // Otherwise remember it in case we see an import for it later.
                            if (isExport) {
                                auto& mnps = subPort->as<ModportNamedPortSyntax>();
                                auto name = mnps.name.valueText();
                                if (name.empty() || nameMap->find(name) != nameMap->end())
                                    break;

                                if (auto it = foundImports.find(name); it != foundImports.end())
                                    create(*it->second);
                                else
                                    waitingForImport.emplace(name);
                            }
                            break;
                        }
                        case SyntaxKind::ModportSubroutinePort: {
                            // If this is an export, see if this should create an implicit
                            // extern prototype. If it's an import then see if a previous
                            // export is waiting for it to be declared.
                            auto& msps = subPort->as<ModportSubroutinePortSyntax>();
                            auto name = msps.prototype->name->getLastToken().valueText();
                            if (name.empty() || nameMap->find(name) != nameMap->end())
                                break;

                            if (isExport) {
                                create(msps);
                            }
                            else {
                                if (waitingForImport.find(name) != waitingForImport.end())
                                    create(msps);
                                else
                                    foundImports.emplace(name, &msps);
                            }
                            break;
                        }
                        default:
                            SLANG_UNREACHABLE;
                    }
                }
            }
        }
    }
}

void Scope::addWildcardImport(const PackageImportItemSyntax& item,
                              std::span<const AttributeInstanceSyntax* const> attributes) {
    if (importData) {
        // Check for redundant import statements.
        for (auto import : importData->wildcardImports) {
            if (import->packageName == item.package.valueText()) {
                if (!import->packageName.empty()) {
                    auto& diag = addDiag(diag::DuplicateImport, item.item.location());
                    diag.addNote(diag::NotePreviousDefinition, import->location);
                }
                return;
            }
        }
    }

    auto import = compilation.emplace<WildcardImportSymbol>(item.package.valueText(),
                                                            item.item.location());

    import->setSyntax(item);
    import->setAttributes(*this, attributes);
    addMember(*import);
    addWildcardImport(*import);
}

void Scope::addWildcardImport(const WildcardImportSymbol& item) {
    if (!importData)
        importData = compilation.allocWildcardImportData();
    importData->wildcardImports.push_back(&item);
}

void Scope::DeferredMemberData::addMember(Symbol* symbol) {
    members.emplace_back(symbol);
}

std::span<Symbol* const> Scope::DeferredMemberData::getMembers() const {
    return members;
}

void Scope::DeferredMemberData::addForwardingTypedef(const ForwardingTypedefSymbol& symbol) {
    forwardingTypedefs.push_back(&symbol);
}

std::span<const ForwardingTypedefSymbol* const> Scope::DeferredMemberData::getForwardingTypedefs()
    const {
    return forwardingTypedefs;
}

void Scope::DeferredMemberData::addPortDeclaration(const SyntaxNode& syntax,
                                                   const Symbol* insertion) {
    portDecls.emplace_back(&syntax, insertion);
}

std::span<std::pair<const SyntaxNode*, const Symbol*> const> Scope::DeferredMemberData::
    getPortDeclarations() const {
    return portDecls;
}

static size_t countGenMembers(const SyntaxNode& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::IfGenerate: {
            auto& ifGen = syntax.as<IfGenerateSyntax>();
            size_t count = countGenMembers(*ifGen.block);
            if (ifGen.elseClause)
                count += countGenMembers(*ifGen.elseClause->clause);

            return count;
        }
        case SyntaxKind::CaseGenerate: {
            auto& caseGen = syntax.as<CaseGenerateSyntax>();
            size_t count = 0;
            for (auto item : caseGen.items) {
                switch (item->kind) {
                    case SyntaxKind::StandardCaseItem:
                        count += countGenMembers(*item->as<StandardCaseItemSyntax>().clause);
                        break;
                    case SyntaxKind::DefaultCaseItem:
                        count += countGenMembers(*item->as<DefaultCaseItemSyntax>().clause);
                        break;
                    default:
                        SLANG_UNREACHABLE;
                }
            }
            return count;
        }
        default: {
            return 1;
        }
    }
}

static size_t countBindMembers(const BindDirectiveSyntax& syntax) {
    if (syntax.instantiation->kind == SyntaxKind::CheckerInstantiation)
        return syntax.instantiation->as<CheckerInstantiationSyntax>().instances.size();
    else
        return syntax.instantiation->as<HierarchyInstantiationSyntax>().instances.size();
}

static size_t countMembers(const SyntaxNode& syntax) {
    // Note that the +1s on some of these are to make a slot for implicit
    // nets that get created to live.
    switch (syntax.kind) {
        case SyntaxKind::HierarchyInstantiation:
            return syntax.as<HierarchyInstantiationSyntax>().instances.size() + 1;
        case SyntaxKind::PrimitiveInstantiation:
            return syntax.as<PrimitiveInstantiationSyntax>().instances.size() + 1;
        case SyntaxKind::CheckerInstantiation:
            return syntax.as<CheckerInstantiationSyntax>().instances.size() + 1;
        case SyntaxKind::ContinuousAssign:
            return syntax.as<ContinuousAssignSyntax>().assignments.size() + 1;
        case SyntaxKind::AnsiPortList:
            return syntax.as<AnsiPortListSyntax>().ports.size();
        case SyntaxKind::NonAnsiPortList:
            return syntax.as<NonAnsiPortListSyntax>().ports.size();
        case SyntaxKind::ModportDeclaration:
            return syntax.as<ModportDeclarationSyntax>().items.size();
        case SyntaxKind::DataDeclaration:
            return syntax.as<DataDeclarationSyntax>().declarators.size();
        case SyntaxKind::PortDeclaration:
            return syntax.as<PortDeclarationSyntax>().declarators.size();
        case SyntaxKind::ClockingItem:
            return syntax.as<ClockingItemSyntax>().decls.size();
        case SyntaxKind::IfGenerate:
        case SyntaxKind::CaseGenerate:
            return countGenMembers(syntax);
        case SyntaxKind::BindDirective:
            return countBindMembers(syntax.as<BindDirectiveSyntax>()) + 1;
        case SyntaxKind::LoopGenerate:
        case SyntaxKind::GenerateBlock:
        case SyntaxKind::DefaultClockingReference:
        case SyntaxKind::DefaultDisableDeclaration:
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::ProgramDeclaration:
        case SyntaxKind::ClassMethodDeclaration:
        case SyntaxKind::EnumType:
            return 1;
        case SyntaxKind::SpecifyBlock:
        case SyntaxKind::CoverCross:
        case SyntaxKind::NetAlias:
            return 2;
        default:
            SLANG_UNREACHABLE;
    }
}

} // namespace slang::ast
