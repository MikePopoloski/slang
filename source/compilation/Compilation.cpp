//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Compilation.h"

#include "parsing/SyntaxTree.h"

namespace slang {

Compilation::Compilation() :
    shortIntType(BuiltInIntegerType::ShortInt),
    intType(BuiltInIntegerType::Int),
    longIntType(BuiltInIntegerType::LongInt),
    byteType(BuiltInIntegerType::Byte),
    bitType(BuiltInIntegerType::Bit),
    logicType(BuiltInIntegerType::Logic),
    regType(BuiltInIntegerType::Reg),
    integerType(BuiltInIntegerType::Integer),
    timeType(BuiltInIntegerType::Time),
    realType(FloatingType::Real),
    realTimeType(FloatingType::RealTime),
    shortRealType(FloatingType::ShortReal)
{
    // Register built-in types for lookup by syntax kind.
    knownTypes[SyntaxKind::ShortIntType] = &shortIntType;
    knownTypes[SyntaxKind::IntType] = &intType;
    knownTypes[SyntaxKind::LongIntType] = &longIntType;
    knownTypes[SyntaxKind::ByteType] = &byteType;
    knownTypes[SyntaxKind::BitType] = &bitType;
    knownTypes[SyntaxKind::LogicType] = &logicType;
    knownTypes[SyntaxKind::RegType] = &regType;
    knownTypes[SyntaxKind::IntegerType] = &integerType;
    knownTypes[SyntaxKind::TimeType] = &timeType;
    knownTypes[SyntaxKind::RealType] = &realType;
    knownTypes[SyntaxKind::RealTimeType] = &realTimeType;
    knownTypes[SyntaxKind::ShortRealType] = &shortRealType;
    knownTypes[SyntaxKind::StringType] = &stringType;
    knownTypes[SyntaxKind::CHandleType] = &chandleType;
    knownTypes[SyntaxKind::VoidType] = &voidType;
    knownTypes[SyntaxKind::EventType] = &eventType;
    knownTypes[SyntaxKind::Unknown] = &errorType;

    root.reset(new RootSymbol(*this));

    // Register known system functions with the root symbol.
    root->addMember(createSystemFunction("$clog2", SystemFunction::clog2, { &getIntType() }));

    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    const auto& trivialIntType = getType(1, false, true);
    root->addMember(createSystemFunction("$bits", SystemFunction::bits, { &trivialIntType }));
    root->addMember(createSystemFunction("$left", SystemFunction::left, { &trivialIntType }));
    root->addMember(createSystemFunction("$right", SystemFunction::right, { &trivialIntType }));
    root->addMember(createSystemFunction("$low", SystemFunction::low, { &trivialIntType }));
    root->addMember(createSystemFunction("$high", SystemFunction::high, { &trivialIntType }));
    root->addMember(createSystemFunction("$size", SystemFunction::size, { &trivialIntType }));
    root->addMember(createSystemFunction("$increment", SystemFunction::increment, { &trivialIntType }));
}

void Compilation::addSyntaxTree(const SyntaxTree& tree) {
    if (finalized)
        throw std::logic_error("The compilation has already been finalized");

    auto unit = emplace<CompilationUnitSymbol>(*this);
    const SyntaxNode& node = tree.root();
    NameSet instances;

    if (node.kind == SyntaxKind::CompilationUnit) {
        for (auto member : node.as<CompilationUnitSyntax>().members) {
            unit->addMembers(*member);

            // Because of the requirement that we look at uninstantiated branches of generate blocks,
            // we need to look at the syntax nodes instead of any bound symbols.
            if (member->kind == SyntaxKind::ModuleDeclaration) {
                SmallVectorSized<NameSet, 2> scopeStack;
                findInstantiations(member->as<MemberSyntax>(), scopeStack, instances);
            }
        }
    }
    else {
        unit->addMembers(node);

        if (node.kind == SyntaxKind::ModuleDeclaration) {
            SmallVectorSized<NameSet, 2> scopeStack;
            findInstantiations(node.as<MemberSyntax>(), scopeStack, instances);
        }
    }

    // Merge found instantiations into the global list. This is done separately instead of
    // just passing instantiatedNames into findInstantiations to make it easy in the future
    // to make this method thread safe by throwing a lock around this stuff.
    for (auto entry : instances)
        instantiatedNames.emplace(entry);

    // Keep track of any newly created definitions in the root symbol's name map.
    for (auto symbol : unit->members()) {
        switch (symbol->kind) {
            case SymbolKind::Module:
            case SymbolKind::Interface:
            case SymbolKind::Program:
                addDefinition(symbol->as<DefinitionSymbol>());
                break;
            case SymbolKind::Package:
                // Track packages separately; they live in their own namespace.
                addPackage(symbol->as<PackageSymbol>());
                break;
            default:
                break;
        }
    }

    root->addMember(*unit);
    compilationUnits.push_back(unit);
}

const RootSymbol& Compilation::getRoot() {
    if (!finalized) {
        // Find modules that have no instantiations.
        SmallVectorSized<const ModuleInstanceSymbol*, 4> topList;
        for (auto& [name, definition] : definitionMap) {
            if (definition->kind == SymbolKind::Module && instantiatedNames.count(definition->name) == 0) {
                // TODO: check for no parameters here
                auto instance = emplace<ModuleInstanceSymbol>(*this, name, *definition);
                root->addMember(*instance);
                topList.append(instance);

                // Copy in all members from the definition into the instance.
                for (auto member : instance->definition.members())
                    instance->addMember(member->clone());
            }
        }

        // Sort the list of instances so that we get deterministic ordering of instances;
        // the order is otherwise dependent on iterating over a hash table.
        std::sort(topList.begin(), topList.end(), [](auto a, auto b) { return a->name < b->name; });

        root->topInstances = topList.copy(*this);
        root->compilationUnits = compilationUnits;
        finalized = true;
    }
    return *root;
}

const DefinitionSymbol* Compilation::getDefinition(string_view lookupName) const {
    auto it = definitionMap.find(lookupName);
    if (it == definitionMap.end())
        return nullptr;
    return it->second;
}

void Compilation::addDefinition(const DefinitionSymbol& definition) {
    definitionMap.emplace(definition.name, &definition);
}

const PackageSymbol* Compilation::getPackage(string_view lookupName) const {
    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;
    return it->second;
}

void Compilation::addPackage(const PackageSymbol& package) {
    packageMap.emplace(package.name, &package);
}

CompilationUnitSymbol& Compilation::createScriptScope() {
    auto unit = emplace<CompilationUnitSymbol>(*this);
    root->addMember(*unit);
    return *unit;
}

static VectorType::ScalarType getScalarType(bool isFourState, bool isReg) {
    return !isFourState ? VectorType::Bit : isReg ? VectorType::Reg : VectorType::Logic;
}

const Type& Compilation::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? errorType : *it->second;
}

const Type& Compilation::getType(const DataTypeSyntax& node, const Scope& parent) {
    switch (node.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return IntegralType::fromSyntax(*this, node.as<IntegerTypeSyntax>(), parent);
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            // TODO: signing
            // TODO: report this error in the parser?
            //auto& its = syntax.as<IntegerTypeSyntax>();
            //if (its.dimensions.count() > 0) {
            //    // Error but don't fail out; just remove the dims and keep trucking
            //    auto& diag = addError(DiagCode::PackedDimsOnPredefinedType, its.dimensions[0]->openBracket.location());
            //    diag << getTokenKindText(its.keyword.kind);
            //}
            return getType(node.kind);
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
            return getType(node.kind);
        default:
            THROW_UNREACHABLE;
    }
}

const VectorType& Compilation::getType(uint16_t width, bool isSigned, bool isFourState, bool isReg) {
    uint32_t key = width;
    key |= uint64_t(isSigned) << 16;
    key |= uint64_t(isFourState) << 17;
    key |= uint64_t(isReg) << 18;

    auto it = vectorTypeCache.find(key);
    if (it != vectorTypeCache.end())
        return *it->second;

    SmallVectorSized<ConstantRange, 2> dims;
    dims.append({ width - 1, 0 });

    auto type = emplace<VectorType>(getScalarType(isFourState, isReg), dims.copy(*this), isSigned);
    vectorTypeCache.emplace_hint(it, key, type);
    return *type;
}

const VectorType& Compilation::getType(bool isSigned, bool isFourState, bool isReg,
                                       span<ConstantRange const> dimensions) {
    return *emplace<VectorType>(getScalarType(isFourState, isReg), dimensions, isSigned);
}

Scope::DeferredMemberData& Compilation::getOrAddDeferredData(Scope::DeferredMemberIndex& index) {
    if (index == Scope::DeferredMemberIndex::Invalid)
        index = deferredData.emplace();
    return deferredData[index];
}

void Compilation::trackImport(Scope::ImportDataIndex& index, const WildcardImportSymbol& import) {
    if (index != Scope::ImportDataIndex::Invalid)
        importData[index].push_back(&import);
    else
        index = importData.add({ &import });
}

span<const WildcardImportSymbol*> Compilation::queryImports(Scope::ImportDataIndex index) {
    if (index == Scope::ImportDataIndex::Invalid)
        return nullptr;
    return importData[index];
}

SubroutineSymbol& Compilation::createSystemFunction(string_view funcName, SystemFunction funcKind,
                                                    std::initializer_list<const Type*> argTypes) {
    auto func = emplace<SubroutineSymbol>(*this, funcName, funcKind);
    func->returnType = getIntType();

    SmallVectorSized<const FormalArgumentSymbol*, 8> args;
    for (auto type : argTypes) {
        auto arg = emplace<FormalArgumentSymbol>();
        arg->type = *type;
        args.append(arg);
    }

    func->arguments = args.copy(*this);
    return *func;
}

void Compilation::findInstantiations(const ModuleDeclarationSyntax& module, SmallVector<NameSet>& scopeStack,
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
                        scopeStack.emplace();
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
        scopeStack.pop();
}

static bool containsName(const SmallVector<flat_hash_set<string_view>>& scopeStack, string_view name) {
    for (const auto& set : scopeStack) {
        if (set.find(name) != set.end())
            return true;
    }
    return false;
}

void Compilation::findInstantiations(const MemberSyntax& node, SmallVector<NameSet>& scopeStack,
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