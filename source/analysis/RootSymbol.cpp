//------------------------------------------------------------------------------
// RootSymbol.cpp
// Root symbol definition.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "RootSymbol.h"

#include "parsing/SyntaxTree.h"

namespace slang {

RootSymbol::RootSymbol(const SourceManager& sourceManager) :
    ScopeSymbol(SymbolKind::Root, *this),
    sourceMan(sourceManager)
{
}

RootSymbol::RootSymbol(const SourceManager& sourceManager, span<const CompilationUnitSyntax* const> units) :
    RootSymbol(sourceManager)
{
    for (auto unit : units)
        addCompilationUnit(allocate<CompilationUnitSymbol>(*unit, *this));
}

RootSymbol::RootSymbol(const SyntaxTree* tree) :
    RootSymbol(make_span(&tree, 1)) {}

RootSymbol::RootSymbol(span<const SyntaxTree* const> trees) :
    RootSymbol(trees[0]->sourceManager())
{
    for (auto tree : trees) {
        ASSERT(&tree->sourceManager() == &sourceMan);
        addCompilationUnit(allocate<CompilationUnitSymbol>(tree->root(), *this));
    }
}

const PackageSymbol* RootSymbol::findPackage(string_view lookupName) const {
    ensureInit();

    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;

    return (const PackageSymbol*)it->second;
}

void RootSymbol::addCompilationUnit(const CompilationUnitSymbol& unit) {
    unitList.push_back(&unit);

    // Track packages separately; they live in their own namespace.
    for (auto symbol : unit.members()) {
        if (symbol->kind == SymbolKind::Package)
            packageMap.emplace(symbol->name, symbol);
    }
}

void RootSymbol::fillMembers(MemberBuilder& builder) const {
    // Register built-in system functions.
    const auto& intType = factory.getIntType();
    SmallVectorSized<const FormalArgumentSymbol*, 8> args;

    args.append(alloc.emplace<FormalArgumentSymbol>(intType, *this));
    builder.add(allocate<SubroutineSymbol>("$clog2", intType, args.copy(alloc), SystemFunction::clog2, *this));

    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    const auto& trivialIntType = factory.getType(1, false, true);
    args.clear();
    args.append(alloc.emplace<FormalArgumentSymbol>(trivialIntType, *this));
    builder.add(allocate<SubroutineSymbol>("$bits", intType, args.copy(alloc), SystemFunction::bits, *this));
    builder.add(allocate<SubroutineSymbol>("$left", intType, args.copy(alloc), SystemFunction::left, *this));
    builder.add(allocate<SubroutineSymbol>("$right", intType, args.copy(alloc), SystemFunction::right, *this));
    builder.add(allocate<SubroutineSymbol>("$low", intType, args.copy(alloc), SystemFunction::low, *this));
    builder.add(allocate<SubroutineSymbol>("$high", intType, args.copy(alloc), SystemFunction::high, *this));
    builder.add(allocate<SubroutineSymbol>("$size", intType, args.copy(alloc), SystemFunction::size, *this));
    builder.add(allocate<SubroutineSymbol>("$increment", intType, args.copy(alloc), SystemFunction::increment, *this));

    // Compute which modules should be automatically instantiated; this is the set of modules that are:
    // 1) declared at the root level
    // 2) never instantiated anywhere in the design (even inside generate blocks that are not selected)
    // 3) don't have any parameters, or all parameters have default values
    //
    // Because of the requirement that we look at uninstantiated branches of generate blocks, we need
    // to look at the syntax nodes instead of any bound symbols.
    NameSet instances;
    for (auto symbol : unitList) {
        for (auto member : symbol->members()) {
            if (member->kind == SymbolKind::Module) {
                builder.add(*member);

                std::vector<NameSet> scopeStack;
                findInstantiations(member->as<DefinitionSymbol>().syntax, scopeStack, instances);
            }
        }
    }

    // Now loop back over and find modules that have no instantiations.
    for (auto symbol : unitList) {
        for (auto member : symbol->members()) {
            if (member->kind == SymbolKind::Module && instances.count(member->name) == 0) {
                // TODO: check for no parameters here
                const auto& instance = allocate<ModuleInstanceSymbol>(member->as<DefinitionSymbol>(), *this);
                builder.add(instance);
                topList.push_back(&instance);
            }
        }
    }
}

void RootSymbol::findInstantiations(const ModuleDeclarationSyntax& module, std::vector<NameSet>& scopeStack,
                                          NameSet& found) {
    // If there are nested modules that shadow global module names, we need to
    // ignore them when considering instantiations.
    NameSet* localDefs = nullptr;
    for (auto member : module.members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                // ignore empty names
                string_view name = member->as<ModuleDeclarationSyntax>().header.name.valueText();
                if (!name.empty()) {
                    // create new scope entry lazily
                    if (!localDefs) {
                        scopeStack.emplace_back();
                        localDefs = &scopeStack.back();
                    }
                    localDefs->insert(name);
                }
                break;
            }
            default:
                break;
        }
    }

    // now traverse all children
    for (auto member : module.members)
        findInstantiations(*member, scopeStack, found);

    if (localDefs)
        scopeStack.pop_back();
}

static bool containsName(const std::vector<std::unordered_set<string_view>>& scopeStack, string_view name) {
    for (const auto& set : scopeStack) {
        if (set.find(name) != set.end())
            return true;
    }
    return false;
}

void RootSymbol::findInstantiations(const MemberSyntax& node, std::vector<NameSet>& scopeStack,
                                          NameSet& found) {
    switch (node.kind) {
        case SyntaxKind::HierarchyInstantiation: {
            // Determine whether this is a local or global module we're instantiating;
            // don't worry about local instantiations right now, they can't be root.
            const auto& his = node.as<HierarchyInstantiationSyntax>();
            string_view name = his.type.valueText();
            if (!name.empty() && !containsName(scopeStack, name))
                found.insert(name);
            break;
        }
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            findInstantiations(node.as<ModuleDeclarationSyntax>(), scopeStack, found);
            break;
        case SyntaxKind::GenerateRegion:
            for (auto& child : node.as<GenerateRegionSyntax>().members)
                findInstantiations(*child, scopeStack, found);
            break;
        case SyntaxKind::GenerateBlock:
            for (auto& child : node.as<GenerateBlockSyntax>().members)
                findInstantiations(*child, scopeStack, found);
            break;
        case SyntaxKind::LoopGenerate:
            findInstantiations(node.as<LoopGenerateSyntax>().block, scopeStack, found);
            break;
        case SyntaxKind::CaseGenerate:
            for (auto& item : node.as<CaseGenerateSyntax>().items) {
                switch (item->kind) {
                    case SyntaxKind::DefaultCaseItem:
                        findInstantiations(item->as<DefaultCaseItemSyntax>().clause.as<MemberSyntax>(),
                                           scopeStack, found);
                        break;
                    case SyntaxKind::StandardCaseItem:
                        findInstantiations(item->as<StandardCaseItemSyntax>().clause.as<MemberSyntax>(),
                                           scopeStack, found);
                        break;
                    default:
                        break;
                }
            }
            break;
        case SyntaxKind::IfGenerate: {
            const auto& ifGen = node.as<IfGenerateSyntax>();
            findInstantiations(ifGen.block, scopeStack, found);
            if (ifGen.elseClause)
                findInstantiations(ifGen.elseClause->clause.as<MemberSyntax>(), scopeStack, found);
            break;
        }
        default:
            break;
    }
}

}