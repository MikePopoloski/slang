//------------------------------------------------------------------------------
// RootSymbol.cpp
// Root symbol definition.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "RootSymbol.h"

#include "parsing/SyntaxTree.h"

namespace slang {

RootSymbol::RootSymbol() :
    Symbol(SymbolKind::Root, *this),
    Scope(this)
{
    init(nullptr);
}

RootSymbol::RootSymbol(span<const CompilationUnitSyntax* const> units) :
    Symbol(SymbolKind::Root, *this),
    Scope(this)
{
    SmallVectorSized<const SyntaxNode*, 16> nodes((uint32_t)units.size());
    for (auto unit : units)
        nodes.append(unit);
    init(nodes);
}

RootSymbol::RootSymbol(const SyntaxTree* tree) :
    RootSymbol(make_span(&tree, 1)) {}

RootSymbol::RootSymbol(span<const SyntaxTree* const> trees) :
    Symbol(SymbolKind::Root, *this),
    Scope(this)
{
    SmallVectorSized<const SyntaxNode*, 16> nodes((uint32_t)trees.size());
    for (auto tree : trees)
        nodes.append(&tree->root());
    init(nodes);
}

const PackageSymbol* RootSymbol::findPackage(string_view lookupName) const {
    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;

    return (const PackageSymbol*)it->second;
}

SubroutineSymbol& RootSymbol::createSystemFunction(string_view funcName, SystemFunction funcKind,
                                                   std::initializer_list<const TypeSymbol*> argTypes) const {
    auto func = alloc.emplace<SubroutineSymbol>(funcName, funcKind, *this);
    func->returnType = factory.getIntType();

    SmallVectorSized<const FormalArgumentSymbol*, 8> args;
    for (auto type : argTypes) {
        auto arg = alloc.emplace<FormalArgumentSymbol>(*func);
        arg->type = *type;
        args.append(arg);
    }

    func->arguments = args.copy(alloc);
    return *func;
}

void RootSymbol::init(span<const SyntaxNode* const> nodes) {
    // Register built-in system functions.
    SmallVectorSized<const Symbol*, 32> symbols;
    symbols.append(&createSystemFunction("$clog2", SystemFunction::clog2, { &factory.getIntType() }));

    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    const auto& trivialIntType = factory.getType(1, false, true);
    symbols.append(&createSystemFunction("$bits", SystemFunction::bits, { &trivialIntType }));
    symbols.append(&createSystemFunction("$left", SystemFunction::left, { &trivialIntType }));
    symbols.append(&createSystemFunction("$right", SystemFunction::right, { &trivialIntType }));
    symbols.append(&createSystemFunction("$low", SystemFunction::low, { &trivialIntType }));
    symbols.append(&createSystemFunction("$high", SystemFunction::high, { &trivialIntType }));
    symbols.append(&createSystemFunction("$size", SystemFunction::size, { &trivialIntType }));
    symbols.append(&createSystemFunction("$increment", SystemFunction::increment, { &trivialIntType }));

    // Go through our list of root nodes and process them. That involves:
    // - creating a CompilationUnitSymbol for each one
    // - pulling packages and definitions out into our own member list
    // - searching the actual syntax tree for instantiations so that we can know the top level instances
    NameSet instances;
    for (auto node : nodes) {
        const auto& unit = factory.createCompilationUnit(*node, *this);
        unitList.push_back(&unit);

        for (auto symbol : unit.members()) {
            switch (symbol->kind) {
                case SymbolKind::Package:
                    // Track packages separately; they live in their own namespace.
                    packageMap.emplace(symbol->name, symbol);
                    break;
                case SymbolKind::Module:
                case SymbolKind::Interface:
                case SymbolKind::Program:
                    symbols.append(symbol);
                    break;
                default:
                    break;
            }
        }

        // Because of the requirement that we look at uninstantiated branches of generate blocks,
        // we need to look at the syntax nodes instead of any bound symbols.
        if (node->kind == SyntaxKind::CompilationUnit) {
            for (auto member : node->as<CompilationUnitSyntax>().members) {
                if (member->kind == SyntaxKind::ModuleDeclaration) {
                    std::vector<NameSet> scopeStack;
                    findInstantiations(member->as<MemberSyntax>(), scopeStack, instances);
                }
            }
        }
        else if (node->kind == SyntaxKind::ModuleDeclaration) {
            std::vector<NameSet> scopeStack;
            findInstantiations(node->as<MemberSyntax>(), scopeStack, instances);
        }
    }

    // Now loop back over and find modules that have no instantiations.
    for (auto symbol : unitList) {
        for (auto member : symbol->members()) {
            if (member->kind == SymbolKind::Module && instances.count(member->name) == 0) {
                // TODO: check for no parameters here
                const auto& definition = member->as<DefinitionSymbol>();
                auto& instance = allocate<ModuleInstanceSymbol>(definition.name, definition, *this);
                topList.push_back(&instance);
            }
        }
    }

    setMembers(symbols);

    // Finally, go back through our list of top-level instances and elaborate their children.
    for (auto instance : topList) {
        // Copy all members from the definition
        symbols.clear();
        for (auto member : instance->definition.members())
            symbols.append(&member->clone(*instance));
        instance->setMembers(symbols);
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