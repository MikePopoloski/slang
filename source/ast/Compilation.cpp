//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"

#include "ElabVisitors.h"
#include <fmt/core.h>
#include <mutex>

#include "slang/ast/ScriptSession.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/CharInfo.h"
#include "slang/text/SourceManager.h"
#include "slang/util/TimeTrace.h"

using namespace slang::parsing;

namespace slang::ast::builtins {

void registerArrayMethods(Compilation&);
void registerConversionFuncs(Compilation&);
void registerCoverageFuncs(Compilation&);
void registerEnumMethods(Compilation&);
void registerMathFuncs(Compilation&);
void registerMiscSystemFuncs(Compilation&);
void registerNonConstFuncs(Compilation&);
void registerQueryFuncs(Compilation&);
void registerStringMethods(Compilation&);
void registerSystemTasks(Compilation&);
void registerGateTypes(Compilation&);
const PackageSymbol& createStdPackage(Compilation&);

} // namespace slang::ast::builtins

namespace slang::ast {

Compilation::Compilation(const Bag& options) :
    options(options.getOrDefault<CompilationOptions>()), driverMapAllocator(*this),
    unrollIntervalMapAllocator(*this), tempDiag({}, {}) {

    // Construct all built-in types.
    bitType = emplace<ScalarType>(ScalarType::Bit);
    logicType = emplace<ScalarType>(ScalarType::Logic);
    intType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Int);
    byteType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Byte);
    integerType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Integer);
    realType = emplace<FloatingType>(FloatingType::Real);
    shortRealType = emplace<FloatingType>(FloatingType::ShortReal);
    stringType = emplace<StringType>();
    voidType = emplace<VoidType>();
    errorType = emplace<ErrorType>();

    auto regType = emplace<ScalarType>(ScalarType::Reg);
    auto signedBitType = emplace<ScalarType>(ScalarType::Bit, true);
    auto signedLogicType = emplace<ScalarType>(ScalarType::Logic, true);
    auto signedRegType = emplace<ScalarType>(ScalarType::Reg, true);
    auto shortIntType = emplace<PredefinedIntegerType>(PredefinedIntegerType::ShortInt);
    auto longIntType = emplace<PredefinedIntegerType>(PredefinedIntegerType::LongInt);
    auto timeType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Time);
    auto realTimeType = emplace<FloatingType>(FloatingType::RealTime);
    auto chandleType = emplace<CHandleType>();
    auto nullType = emplace<NullType>();
    auto eventType = emplace<EventType>();
    auto unboundedType = emplace<UnboundedType>();
    auto typeRefType = emplace<TypeRefType>();
    auto untypedType = emplace<UntypedType>();
    auto sequenceType = emplace<SequenceType>();
    auto propertyType = emplace<PropertyType>();

    // Register built-in types for lookup by syntax kind.
    knownTypes[SyntaxKind::ShortIntType] = shortIntType;
    knownTypes[SyntaxKind::IntType] = intType;
    knownTypes[SyntaxKind::LongIntType] = longIntType;
    knownTypes[SyntaxKind::ByteType] = byteType;
    knownTypes[SyntaxKind::BitType] = bitType;
    knownTypes[SyntaxKind::LogicType] = logicType;
    knownTypes[SyntaxKind::RegType] = regType;
    knownTypes[SyntaxKind::IntegerType] = integerType;
    knownTypes[SyntaxKind::TimeType] = timeType;
    knownTypes[SyntaxKind::RealType] = realType;
    knownTypes[SyntaxKind::RealTimeType] = realTimeType;
    knownTypes[SyntaxKind::ShortRealType] = shortRealType;
    knownTypes[SyntaxKind::StringType] = stringType;
    knownTypes[SyntaxKind::CHandleType] = chandleType;
    knownTypes[SyntaxKind::NullLiteralExpression] = nullType;
    knownTypes[SyntaxKind::VoidType] = voidType;
    knownTypes[SyntaxKind::EventType] = eventType;
    knownTypes[SyntaxKind::WildcardLiteralExpression] = unboundedType;
    knownTypes[SyntaxKind::TypeReference] = typeRefType;
    knownTypes[SyntaxKind::Untyped] = untypedType;
    knownTypes[SyntaxKind::SequenceType] = sequenceType;
    knownTypes[SyntaxKind::PropertyType] = propertyType;
    knownTypes[SyntaxKind::Unknown] = errorType;

#define MAKE_NETTYPE(type)                                               \
    knownNetTypes[TokenKind::type##Keyword] = std::make_unique<NetType>( \
        NetType::type, LexerFacts::getTokenKindText(TokenKind::type##Keyword), *logicType)

    MAKE_NETTYPE(Wire);
    MAKE_NETTYPE(WAnd);
    MAKE_NETTYPE(WOr);
    MAKE_NETTYPE(Tri);
    MAKE_NETTYPE(TriAnd);
    MAKE_NETTYPE(TriOr);
    MAKE_NETTYPE(Tri0);
    MAKE_NETTYPE(Tri1);
    MAKE_NETTYPE(TriReg);
    MAKE_NETTYPE(Supply0);
    MAKE_NETTYPE(Supply1);
    MAKE_NETTYPE(UWire);
    MAKE_NETTYPE(Interconnect);

    knownNetTypes[TokenKind::Unknown] = std::make_unique<NetType>(NetType::Unknown, "<error>",
                                                                  *logicType);
    wireNetType = knownNetTypes[TokenKind::WireKeyword].get();

#undef MAKE_NETTYPE

    // Scalar types are indexed by bit flags.
    auto registerScalar = [this](auto type) {
        scalarTypeTable[type->getIntegralFlags().bits() & 0x7] = type;
    };
    registerScalar(bitType);
    registerScalar(logicType);
    registerScalar(regType);
    registerScalar(signedBitType);
    registerScalar(signedLogicType);
    registerScalar(signedRegType);

    root = std::make_unique<RootSymbol>(*this);

    // Register all system tasks, functions, and methods.
    builtins::registerArrayMethods(*this);
    builtins::registerConversionFuncs(*this);
    builtins::registerCoverageFuncs(*this);
    builtins::registerEnumMethods(*this);
    builtins::registerMathFuncs(*this);
    builtins::registerMiscSystemFuncs(*this);
    builtins::registerNonConstFuncs(*this);
    builtins::registerQueryFuncs(*this);
    builtins::registerStringMethods(*this);
    builtins::registerSystemTasks(*this);

    // Register the built-in std package.
    stdPkg = &builtins::createStdPackage(*this);
    packageMap.emplace(stdPkg->name, stdPkg);

    // Register the built-in gate types.
    builtins::registerGateTypes(*this);

    // Set a default handler for printing types and symbol paths, for convenience.
    static std::once_flag onceFlag;
    std::call_once(onceFlag, [] {
        DiagnosticEngine::setDefaultFormatter<const Type*>(std::make_unique<TypeArgFormatter>());
        TextDiagnosticClient::setDefaultSymbolPathCB([](const Symbol& sym) {
            std::string str;
            sym.getHierarchicalPath(str);
            return str;
        });
    });

    // Reset systemId counters that may have been changed due to creation of types
    // in the std package.
    nextEnumSystemId = 1;
    nextStructSystemId = 1;
    nextUnionSystemId = 1;
}

Compilation::~Compilation() = default;

void Compilation::addSyntaxTree(std::shared_ptr<SyntaxTree> tree) {
    if (!tree)
        SLANG_THROW(std::invalid_argument("tree cannot be null"));

    if (finalized)
        SLANG_THROW(std::logic_error("The compilation has already been finalized"));

    if (&tree->sourceManager() != sourceManager) {
        if (!sourceManager)
            sourceManager = &tree->sourceManager();
        else {
            SLANG_THROW(std::logic_error(
                "All syntax trees added to the compilation must use the same source manager"));
        }
    }

    const SyntaxNode& node = tree->root();
    const SyntaxNode* topNode = &node;
    while (topNode->parent)
        topNode = topNode->parent;

    auto unit = emplace<CompilationUnitSymbol>(*this);
    unit->setSyntax(*topNode);
    root->addMember(*unit);
    compilationUnits.push_back(unit);

    for (auto& [n, meta] : tree->getMetadata().nodeMap) {
        SyntaxMetadata result;
        result.tree = tree.get();
        result.library = meta.library;
        result.defaultNetType = &getNetType(meta.defaultNetType);
        result.timeScale = meta.timeScale;

        switch (meta.unconnectedDrive) {
            case TokenKind::Pull0Keyword:
                result.unconnectedDrive = UnconnectedDrive::Pull0;
                break;
            case TokenKind::Pull1Keyword:
                result.unconnectedDrive = UnconnectedDrive::Pull1;
                break;
            default:
                result.unconnectedDrive = UnconnectedDrive::None;
                break;
        }

        syntaxMetadata[n] = result;
        if (result.library)
            libraryNameMap[result.library->name] = result.library;
    }

    for (auto& name : tree->getMetadata().globalInstances)
        globalInstantiations.emplace(name);

    if (node.kind == SyntaxKind::CompilationUnit) {
        for (auto member : node.as<CompilationUnitSyntax>().members)
            unit->addMembers(*member);
    }
    else if (node.kind == SyntaxKind::LibraryMap) {
        for (auto member : node.as<LibraryMapSyntax>().members)
            unit->addMembers(*member);
    }
    else {
        unit->addMembers(node);
    }

    syntaxTrees.emplace_back(std::move(tree));
    cachedParseDiagnostics.reset();
}

std::span<const std::shared_ptr<SyntaxTree>> Compilation::getSyntaxTrees() const {
    return syntaxTrees;
}

std::span<const CompilationUnitSymbol* const> Compilation::getCompilationUnits() const {
    return compilationUnits;
}

std::vector<const DefinitionSymbol*> Compilation::getDefinitions() const {
    std::vector<const DefinitionSymbol*> result;
    for (auto& def : definitionMemory)
        result.push_back(def.get());
    return result;
}

std::vector<const PackageSymbol*> Compilation::getPackages() const {
    std::vector<const PackageSymbol*> result;
    for (auto& [name, pkg] : packageMap)
        result.push_back(pkg);
    return result;
}

std::vector<const PrimitiveSymbol*> Compilation::getPrimitives() const {
    std::vector<const PrimitiveSymbol*> result;
    for (auto& [name, prim] : udpMap)
        result.push_back(prim);
    return result;
}

const SourceLibrary* Compilation::getSourceLibrary(std::string_view name) const {
    if (auto it = libraryNameMap.find(name); it != libraryNameMap.end())
        return it->second;
    return nullptr;
}

const RootSymbol& Compilation::getRoot() {
    return getRoot(/* skipDefParamsAndBinds */ false);
}

const RootSymbol& Compilation::getRoot(bool skipDefParamsAndBinds) {
    if (finalized)
        return *root;

    // Resolve default lib list now that we have all syntax trees added.
    defaultLiblist.reserve(options.defaultLiblist.size());
    for (auto& libName : options.defaultLiblist) {
        if (auto lib = getSourceLibrary(libName))
            defaultLiblist.push_back(lib);
    }

    // If any top-level parameter overrides were provided, parse them now.
    flat_hash_map<std::string_view, const ConstantValue*> cliOverrides;
    parseParamOverrides(cliOverrides);

    // If there are defparams we need to fully resolve their values up front before
    // we start elaborating any instances.
    if (!skipDefParamsAndBinds) {
        for (auto& tree : syntaxTrees) {
            auto& meta = tree->getMetadata();
            if (meta.hasDefparams || meta.hasBindDirectives) {
                resolveDefParamsAndBinds();
                break;
            }
        }
    }

    SLANG_ASSERT(!finalizing);
    finalizing = true;
    auto guard = ScopeGuard([this] { finalizing = false; });

    auto isValidTop = [&](auto& definition) {
        // All parameters must have defaults.
        for (auto& param : definition.parameters) {
            if (!param.hasDefault() &&
                (param.isTypeParam || cliOverrides.find(param.name) == cliOverrides.end())) {
                return false;
            }
        }
        return true;
    };

    // Find top level modules (and programs) that form the root of the design.
    // Iterate the definitions map before instantiating any top level modules,
    // since that can cause changes to the definition map itself.
    SmallVector<std::pair<const DefinitionSymbol*, const ConfigBlockSymbol*>> topDefs;
    SmallSet<const ConfigBlockSymbol*, 2> selectedConfigs;
    if (options.topModules.empty()) {
        for (auto& [key, defList] : definitionMap) {
            if (std::get<1>(key) != root.get())
                continue;

            for (auto def : defList.first) {
                // Ignore definitions that are not top level. Top level definitions are:
                // - Modules and programs
                // - Not nested
                // - Have no non-defaulted parameters
                // - Not instantiated anywhere
                // - Not in a library
                if (def->sourceLibrary ||
                    globalInstantiations.find(def->name) != globalInstantiations.end()) {
                    continue;
                }

                // Library definitions are never automatically instantiated in any capacity.
                if (!def->syntaxTree || !def->syntaxTree->isLibrary) {
                    if (def->definitionKind == DefinitionKind::Module ||
                        def->definitionKind == DefinitionKind::Program) {
                        if (isValidTop(*def)) {
                            // This definition can be automatically instantiated.
                            topDefs.push_back({def, nullptr});
                            continue;
                        }
                    }
                }

                // Otherwise this definition is unreferenced and not automatically instantiated.
                unreferencedDefs.push_back(def);
            }
        }
    }
    else {
        // If the list of top modules has already been provided we just need to
        // find and instantiate them.
        auto& tm = options.topModules;
        for (auto& [key, defList] : definitionMap) {
            if (std::get<1>(key) != root.get())
                continue;

            for (auto def : defList.first) {
                if (def->definitionKind == DefinitionKind::Module ||
                    def->definitionKind == DefinitionKind::Program) {

                    // If this definition is in a library, it can only be targeted as
                    // a top module by the user including the library name in the string.
                    flat_hash_set<std::string_view>::iterator it;
                    if (def->sourceLibrary) {
                        auto target = fmt::format("{}.{}", def->sourceLibrary->name, def->name);
                        it = tm.find(target);
                    }
                    else {
                        it = tm.find(def->name);
                    }

                    if (it != tm.end()) {
                        // Remove from the top modules set so that we know we visited it.
                        tm.erase(it);

                        // Make sure this is actually valid as a top-level module.
                        if (isValidTop(*def)) {
                            topDefs.push_back({def, nullptr});
                            continue;
                        }

                        // Otherwise, issue an error because the user asked us to instantiate this.
                        def->getParentScope()->addDiag(diag::InvalidTopModule,
                                                       SourceLocation::NoLocation)
                            << def->name;
                    }
                }

                // Otherwise this definition might be unreferenced and not automatically
                // instantiated (don't add library definitions to this list though).
                if (globalInstantiations.find(def->name) == globalInstantiations.end() &&
                    !def->sourceLibrary) {
                    unreferencedDefs.push_back(def);
                }
            }
        }

        // Any names still in the map were not found as module definitions.
        for (auto& userProvidedName : tm) {
            // This might be a config block instead. If it has a dot, assume that's
            // the library designator.
            std::string confLib;
            std::string confName(userProvidedName);
            if (auto pos = confName.find_first_of('.'); pos != std::string::npos) {
                confLib = confName.substr(0, pos);
                confName = confName.substr(pos + 1);
            }

            // A trailing ':config' is stripped -- it's there to allow the user
            // to disambiguate modules and config blocks.
            constexpr std::string_view configSuffix = ":config";
            if (confName.ends_with(configSuffix))
                confName = confName.substr(0, confName.length() - configSuffix.length());

            if (auto confIt = configBlocks.find(confName); confIt != configBlocks.end()) {
                const ConfigBlockSymbol* foundConf = nullptr;
                for (auto conf : confIt->second) {
                    if ((!conf->sourceLibrary && confLib.empty()) ||
                        (conf->sourceLibrary && conf->sourceLibrary->name == confLib)) {
                        foundConf = conf;
                        break;
                    }
                }

                if (foundConf) {
                    // TODO: handle other rules for this block
                    const Scope* rootScope = root.get();
                    for (auto& cell : foundConf->topCells) {
                        if (auto defIt = definitionMap.find(std::tuple{cell.name, rootScope});
                            defIt != definitionMap.end()) {

                            const DefinitionSymbol* foundDef = nullptr;
                            for (auto def : defIt->second.first) {
                                if ((cell.lib.empty() &&
                                     def->sourceLibrary == foundConf->sourceLibrary) ||
                                    (def->sourceLibrary && def->sourceLibrary->name == cell.lib)) {
                                    foundDef = def;
                                    break;
                                }
                            }

                            if (foundDef) {
                                selectedConfigs.emplace(foundConf);
                                topDefs.push_back({foundDef, foundConf});
                                continue;
                            }
                        }

                        std::string errorName;
                        if (!cell.lib.empty())
                            errorName = fmt::format("{}.{}", cell.lib, cell.name);
                        else
                            errorName = cell.name;

                        root->addDiag(diag::InvalidTopModule, cell.sourceRange) << errorName;
                    }
                    continue;
                }
            }

            root->addDiag(diag::InvalidTopModule, SourceLocation::NoLocation) << userProvidedName;
        }
    }

    // Sort the list of definitions so that we get deterministic ordering of instances;
    // the order is otherwise dependent on iterating over a hash table.
    std::ranges::sort(topDefs, [](auto a, auto b) { return a.first->name < b.first->name; });
    std::ranges::sort(unreferencedDefs, [](auto a, auto b) { return a->name < b->name; });

    // If we have any cli param overrides we should apply them to
    // each top-level instance.
    // TODO: generalize these to full hierarchical paths
    if (!cliOverrides.empty()) {
        for (auto [def, config] : topDefs) {
            for (auto& param : def->parameters) {
                if (!param.isTypeParam && param.hasSyntax) {
                    auto it = cliOverrides.find(param.name);
                    if (it != cliOverrides.end()) {
                        hierarchyOverrides.childrenBySyntax[*def->getSyntax()]
                            .overridesBySyntax.emplace(param.valueDecl,
                                                       std::pair{*it->second, nullptr});
                    }
                }
            }
        }
    }

    // If there are configs selected we need to apply all instance path
    // rules to our hierarchy overrides before we start creating top instances.
    for (auto config : selectedConfigs) {
        for (auto& instOverride : config->instanceOverrides) {
            HierarchyOverrideNode* node = &hierarchyOverrides;
            HierarchyOverrideNode* prev = node;
            for (auto name : instOverride.path) {
                prev = node;
                node = &node->childrenByName[name];
            }

            node->configRule = &instOverride.rule;
            prev->anyChildConfigRules = true;
        }
    }

    SmallVector<const InstanceSymbol*> topList;
    for (auto [def, config] : topDefs) {
        HierarchyOverrideNode* hierarchyOverrideNode = nullptr;
        if (auto sit = hierarchyOverrides.childrenBySyntax.find(*def->getSyntax());
            sit != hierarchyOverrides.childrenBySyntax.end()) {
            hierarchyOverrideNode = &sit->second;
        }
        else if (auto nit = hierarchyOverrides.childrenByName.find(def->name);
                 nit != hierarchyOverrides.childrenByName.end()) {
            hierarchyOverrideNode = &nit->second;
        }

        auto& instance = InstanceSymbol::createDefault(*this, *def, hierarchyOverrideNode);
        root->addMember(instance);
        topList.push_back(&instance);

        if (config)
            configForScope.emplace(&instance.body, config);
    }

    if (!hasFlag(CompilationFlags::SuppressUnused) && topDefs.empty())
        root->addDiag(diag::NoTopModules, SourceLocation::NoLocation);

    // For unreferenced definitions, go through and instantiate them with all empty
    // parameter values so that we get at least some semantic checking of the contents.
    for (auto def : unreferencedDefs)
        root->addMember(InstanceSymbol::createInvalid(*this, *def));

    root->topInstances = topList.copy(*this);
    root->compilationUnits = compilationUnits;
    finalizing = false;
    finalized = true;

    return *root;
}

const CompilationUnitSymbol* Compilation::getCompilationUnit(
    const CompilationUnitSyntax& syntax) const {

    for (auto unit : compilationUnits) {
        if (unit->getSyntax() == &syntax)
            return unit;
    }
    return nullptr;
}

const DefinitionSymbol* Compilation::getDefinition(std::string_view lookupName,
                                                   const Scope& scope) const {
    // Try to find a config block for this scope to help choose the right definition.
    const ConfigBlockSymbol* config = nullptr;
    if (!configForScope.empty()) {
        auto searchScope = &scope;
        do {
            auto it = configForScope.find(searchScope);
            if (it != configForScope.end()) {
                config = it->second;
                break;
            }

            searchScope = searchScope->asSymbol().getParentScope();
        } while (searchScope);
    }

    // Always search in the root scope to start. Most definitions are global.
    auto it = definitionMap.find({lookupName, root.get()});
    if (it == definitionMap.end()) {
        // If there's a config it might be able to provide an
        // override for this cell name.
        if (config)
            return resolveConfigRules(lookupName, scope, config, nullptr, {});
        return nullptr;
    }

    // If the second flag is set it means there are nested modules
    // with this name, so we need to do full scope resolution.
    if (it->second.second) {
        auto searchScope = &scope;
        do {
            auto scopeIt = definitionMap.find({lookupName, searchScope});
            if (scopeIt != definitionMap.end()) {
                it = scopeIt;
                break;
            }

            searchScope = searchScope->asSymbol().getParentScope();
        } while (searchScope && searchScope != root.get());
    }

    auto& defList = it->second.first;
    if (config)
        return resolveConfigRules(lookupName, scope, config, nullptr, defList);

    // If there is a global priority list try to use that.
    for (auto lib : defaultLiblist) {
        for (auto def : defList) {
            if (def->sourceLibrary == lib)
                return def;
        }
    }

    // Otherwise return the first definition in the list -- it's already
    // sorted in priority order.
    return defList.empty() ? nullptr : defList.front();
}

const DefinitionSymbol* Compilation::getDefinition(const ModuleDeclarationSyntax& syntax) const {
    if (auto it = definitionFromSyntax.find(&syntax); it != definitionFromSyntax.end()) {
        // If this definition is no longer referenced by the definitionMap
        // it probably got booted by an (illegal) duplicate definition.
        // We don't want to return anything in that case.
        auto def = it->second;
        auto& defScope = *def->getParentScope();
        auto targetScope = defScope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get()
                                                                                   : &defScope;

        auto dmIt = definitionMap.find(std::make_tuple(def->name, targetScope));
        if (dmIt != definitionMap.end() &&
            std::ranges::find(dmIt->second.first, def) != dmIt->second.first.end()) {
            return def;
        }
    }
    return nullptr;
}

const DefinitionSymbol* Compilation::getDefinition(std::string_view lookupName, const Scope& scope,
                                                   const ConfigRule& configRule) const {
    // TODO: handle error cases
    auto it = definitionMap.find({lookupName, root.get()});
    if (it == definitionMap.end())
        return resolveConfigRules(lookupName, scope, nullptr, &configRule, {});
    else
        return resolveConfigRules(lookupName, scope, nullptr, &configRule, it->second.first);
}

template<typename T>
static void reportRedefinition(const Scope& scope, const T& newSym, SourceLocation oldLoc,
                               DiagCode code) {
    if (!newSym.name.empty()) {
        auto& diag = scope.addDiag(code, newSym.location);
        diag << newSym.name;
        diag.addNote(diag::NotePreviousDefinition, oldLoc);
    }
}

static void checkExternModMatch(const Scope& scope, const ModuleHeaderSyntax& externNode,
                                const ModuleHeaderSyntax& prevNode, DiagCode code) {
    auto isEmptyPortList = [](const PortListSyntax* pls) {
        return !pls || (pls->kind == SyntaxKind::NonAnsiPortList &&
                        pls->as<NonAnsiPortListSyntax>().ports.empty());
    };

    const bool prevIsWildcard = prevNode.ports &&
                                prevNode.ports->kind == SyntaxKind::WildcardPortList;

    bool portsMatch;
    if (prevIsWildcard)
        portsMatch = true;
    else if (bool(externNode.ports) == bool(prevNode.ports))
        portsMatch = !externNode.ports || externNode.ports->isEquivalentTo(*prevNode.ports);
    else
        portsMatch = isEmptyPortList(externNode.ports) && isEmptyPortList(prevNode.ports);

    bool paramsMatch;
    if (prevIsWildcard)
        paramsMatch = true;
    else if (bool(externNode.parameters) != bool(prevNode.parameters))
        paramsMatch = false;
    else {
        paramsMatch = !externNode.parameters ||
                      externNode.parameters->isEquivalentTo(*prevNode.parameters);
    }

    if (!portsMatch || !paramsMatch ||
        externNode.moduleKeyword.kind != prevNode.moduleKeyword.kind) {
        auto& diag = scope.addDiag(code, externNode.sourceRange());
        diag << externNode.moduleKeyword.valueText() << externNode.name.valueText();
        diag.addNote(diag::NotePreviousDefinition, prevNode.sourceRange());
    }
}

static void checkExternUdpMatch(const Scope& scope, const UdpPortListSyntax& externNode,
                                const UdpPortListSyntax& prevNode, std::string_view name,
                                DiagCode code) {
    if (prevNode.kind != SyntaxKind::WildcardUdpPortList && !externNode.isEquivalentTo(prevNode)) {
        auto& diag = scope.addDiag(code, externNode.sourceRange());
        diag << "primitive"sv << name;
        diag.addNote(diag::NotePreviousDefinition, prevNode.sourceRange());
    }
}

void Compilation::createDefinition(const Scope& scope, LookupLocation location,
                                   const ModuleDeclarationSyntax& syntax) {
    // We can only be missing metadata if the definition is created programmatically
    // (i.e. not via the parser) so we just fill in the parent's default net type
    // so that it's not a null pointer.
    auto& metadata = syntaxMetadata[&syntax];
    if (!metadata.defaultNetType)
        metadata.defaultNetType = &scope.getDefaultNetType();

    auto def = definitionMemory
                   .emplace_back(std::make_unique<DefinitionSymbol>(
                       scope, location, syntax, *metadata.defaultNetType, metadata.unconnectedDrive,
                       metadata.timeScale, metadata.tree, metadata.library))
                   .get();
    definitionFromSyntax[&syntax] = def;

    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    const bool isRoot = targetScope == root.get();

    auto key = std::tuple(def->name, targetScope);
    auto it = definitionMap.find(key);
    if (it == definitionMap.end()) {
        definitionMap.emplace(key, std::pair{std::vector{def}, !isRoot});
    }
    else {
        // There is already a definition with this name in this scope.
        // If we're not at the root scope, it's a straightforward error.
        auto& defList = it->second.first;
        if (!isRoot) {
            reportRedefinition(scope, *def, defList[0]->location, diag::DuplicateDefinition);
            return;
        }

        // Otherwise, if they're in the same source library we take the
        // latter one (with a warning) and if not then we store both
        // and resolve them later via config or library ordering.
        auto vecIt =
            std::ranges::lower_bound(defList, def, [](DefinitionSymbol* a, DefinitionSymbol* b) {
                if (!a->sourceLibrary)
                    return false;
                if (!b->sourceLibrary)
                    return true;
                return a->sourceLibrary->priority < b->sourceLibrary->priority;
            });

        if (vecIt != defList.end() && (*vecIt)->sourceLibrary == def->sourceLibrary) {
            // TODO: take the second one instead of the first?
            reportRedefinition(scope, *def, (*vecIt)->location, diag::DuplicateDefinition);
            return;
        }

        defList.insert(vecIt, def);
    }

    if (isRoot) {
        if (auto primIt = udpMap.find(def->name); primIt != udpMap.end())
            reportRedefinition(scope, *def, primIt->second->location, diag::Redefinition);
        else if (auto prim = getExternPrimitive(def->name, scope))
            reportRedefinition(scope, *def, prim->name.location(), diag::Redefinition);
        else if (auto externMod = getExternModule(def->name, scope)) {
            // TODO: how do extern modules work with libraries?
            checkExternModMatch(scope, *externMod->header, *syntax.header,
                                diag::ExternDeclMismatchImpl);
        }

        checkElemTimeScale(def->timeScale, syntax.header->name.range());
    }
    else {
        // Record the fact that we have nested modules with this given name.
        definitionMap[std::tuple(def->name, root.get())].second = true;
    }
}

const PackageSymbol* Compilation::getPackage(std::string_view lookupName) const {
    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;
    return it->second;
}

const PackageSymbol& Compilation::createPackage(const Scope& scope,
                                                const ModuleDeclarationSyntax& syntax) {
    auto& metadata = syntaxMetadata[&syntax];
    if (!metadata.defaultNetType)
        metadata.defaultNetType = &scope.getDefaultNetType();

    auto& package = PackageSymbol::fromSyntax(scope, syntax, *metadata.defaultNetType,
                                              metadata.timeScale);

    auto [it, inserted] = packageMap.emplace(package.name, &package);
    if (!inserted && !package.name.empty() &&
        scope.asSymbol().kind == SymbolKind::CompilationUnit) {
        auto& diag = scope.addDiag(diag::Redefinition, package.location);
        diag << package.name;
        diag.addNote(diag::NotePreviousDefinition, it->second->location);
    }

    checkElemTimeScale(package.timeScale, syntax.header->name.range());

    return package;
}

const ConfigBlockSymbol& Compilation::createConfigBlock(const Scope& scope,
                                                        const ConfigDeclarationSyntax& syntax) {
    auto& metadata = syntaxMetadata[&syntax];
    auto& config = ConfigBlockSymbol::fromSyntax(scope, syntax);
    config.sourceLibrary = metadata.library;

    auto it = configBlocks.find(config.name);
    if (it == configBlocks.end()) {
        configBlocks.emplace(config.name, std::vector<const ConfigBlockSymbol*>{&config});
    }
    else {
        auto findIt = std::ranges::find_if(it->second, [&](const ConfigBlockSymbol* elem) {
            return elem->sourceLibrary == config.sourceLibrary;
        });

        if (findIt != it->second.end()) {
            auto& diag = scope.addDiag(diag::Redefinition, config.location);
            diag << config.name;
            diag.addNote(diag::NotePreviousDefinition, (*findIt)->location);
        }
        else {
            it->second.emplace_back(&config);
        }
    }

    return config;
}

const PrimitiveSymbol* Compilation::getPrimitive(std::string_view lookupName) const {
    if (auto it = udpMap.find(lookupName); it != udpMap.end())
        return it->second;
    return nullptr;
}

const PrimitiveSymbol& Compilation::createPrimitive(const Scope& scope,
                                                    const UdpDeclarationSyntax& syntax) {
    // TODO: handle primitives in libraries
    auto& prim = PrimitiveSymbol::fromSyntax(scope, syntax);
    if (!prim.name.empty()) {
        auto [it, inserted] = udpMap.emplace(prim.name, &prim);
        if (!inserted) {
            reportRedefinition(*root, prim, it->second->location, diag::DuplicateDefinition);
        }
        else {
            if (auto defIt = definitionMap.find({prim.name, root.get()});
                defIt != definitionMap.end() && !defIt->second.first.empty()) {
                // TODO: only error for same library?
                reportRedefinition(*root, prim, defIt->second.first.front()->location,
                                   diag::Redefinition);
            }
            else if (auto externMod = getExternModule(prim.name, scope)) {
                reportRedefinition(*root, prim, externMod->header->name.location(),
                                   diag::Redefinition);
            }
            else if (auto externPrim = getExternPrimitive(prim.name, scope)) {
                checkExternUdpMatch(scope, *externPrim->portList, *syntax.portList, prim.name,
                                    diag::ExternDeclMismatchImpl);
            }
        }
    }

    return prim;
}

const PrimitiveSymbol* Compilation::getGateType(std::string_view lookupName) const {
    if (auto it = gateMap.find(lookupName); it != gateMap.end())
        return it->second;
    return nullptr;
}

void Compilation::addGateType(const PrimitiveSymbol& prim) {
    SLANG_ASSERT(!prim.name.empty());
    gateMap.emplace(prim.name, &prim);
}

void Compilation::addSystemSubroutine(std::unique_ptr<SystemSubroutine> subroutine) {
    subroutineMap.emplace(subroutine->name, subroutine.get());
    subroutineStorage.emplace_back(std::move(subroutine));
}

void Compilation::addSystemSubroutine(const SystemSubroutine& subroutine) {
    subroutineMap.emplace(subroutine.name, &subroutine);
}

void Compilation::addSystemMethod(SymbolKind typeKind, std::unique_ptr<SystemSubroutine> method) {
    methodMap.emplace(std::make_tuple(std::string_view(method->name), typeKind), method.get());
    subroutineStorage.emplace_back(std::move(method));
}

void Compilation::addSystemMethod(SymbolKind typeKind, const SystemSubroutine& method) {
    methodMap.emplace(std::make_tuple(std::string_view(method.name), typeKind), &method);
}

const SystemSubroutine* Compilation::getSystemSubroutine(std::string_view name) const {
    auto it = subroutineMap.find(name);
    if (it == subroutineMap.end())
        return nullptr;
    return it->second;
}

const SystemSubroutine* Compilation::getSystemMethod(SymbolKind typeKind,
                                                     std::string_view name) const {
    auto it = methodMap.find(std::make_tuple(name, typeKind));
    if (it == methodMap.end())
        return nullptr;
    return it->second;
}

void Compilation::setAttributes(const Symbol& symbol,
                                std::span<const AttributeSymbol* const> attributes) {
    attributeMap[&symbol] = attributes;
}

void Compilation::setAttributes(const Statement& stmt,
                                std::span<const AttributeSymbol* const> attributes) {
    attributeMap[&stmt] = attributes;
}

void Compilation::setAttributes(const Expression& expr,
                                std::span<const AttributeSymbol* const> attributes) {
    attributeMap[&expr] = attributes;
}

void Compilation::setAttributes(const PortConnection& conn,
                                std::span<const AttributeSymbol* const> attributes) {
    attributeMap[&conn] = attributes;
}

std::span<const AttributeSymbol* const> Compilation::getAttributes(const Symbol& symbol) const {
    return getAttributes(static_cast<const void*>(&symbol));
}

std::span<const AttributeSymbol* const> Compilation::getAttributes(const Statement& stmt) const {
    return getAttributes(static_cast<const void*>(&stmt));
}

std::span<const AttributeSymbol* const> Compilation::getAttributes(const Expression& expr) const {
    return getAttributes(static_cast<const void*>(&expr));
}

std::span<const AttributeSymbol* const> Compilation::getAttributes(
    const PortConnection& conn) const {
    return getAttributes(static_cast<const void*>(&conn));
}

std::span<const AttributeSymbol* const> Compilation::getAttributes(const void* ptr) const {
    auto it = attributeMap.find(ptr);
    if (it == attributeMap.end())
        return {};

    return it->second;
}

void Compilation::notePackageExportCandidate(const PackageSymbol& packageScope,
                                             const Symbol& symbol) {
    packageExportCandidateMap[&packageScope][symbol.name] = &symbol;
}

const Symbol* Compilation::findPackageExportCandidate(const PackageSymbol& packageScope,
                                                      std::string_view name) const {
    if (auto it = packageExportCandidateMap.find(&packageScope);
        it != packageExportCandidateMap.end()) {
        if (auto symIt = it->second.find(name); symIt != it->second.end())
            return symIt->second;
    }
    return nullptr;
}

void Compilation::noteBindDirective(const BindDirectiveSyntax& syntax, const Scope& scope) {
    bindDirectives.emplace_back(&syntax, &scope);
}

void Compilation::noteInstanceWithDefBind(const Symbol& instance) {
    auto& def = instance.as<InstanceBodySymbol>().getDefinition();
    instancesWithDefBinds[&def].push_back(&instance);
}

void Compilation::noteDPIExportDirective(const DPIExportSyntax& syntax, const Scope& scope) {
    dpiExports.emplace_back(&syntax, &scope);
}

void Compilation::addOutOfBlockDecl(const Scope& scope, const ScopedNameSyntax& name,
                                    const SyntaxNode& syntax, SymbolIndex index) {
    std::string_view className = name.left->getLastToken().valueText();
    std::string_view declName = name.right->getLastToken().valueText();
    auto [it, inserted] = outOfBlockDecls.emplace(std::make_tuple(className, declName, &scope),
                                                  std::make_tuple(&syntax, &name, index, false));

    if (!inserted && !className.empty() && !declName.empty()) {
        std::string combined = fmt::format("{}::{}", className, declName);
        auto range = std::get<1>(it->second)->sourceRange();

        auto& diag = scope.addDiag(diag::Redefinition, name.sourceRange());
        diag << combined;
        diag.addNote(diag::NotePreviousDefinition, range);
    }
}

std::tuple<const SyntaxNode*, SymbolIndex, bool*> Compilation::findOutOfBlockDecl(
    const Scope& scope, std::string_view className, std::string_view declName) const {

    auto it = outOfBlockDecls.find({className, declName, &scope});
    if (it != outOfBlockDecls.end()) {
        auto& [syntax, name, index, used] = it->second;
        return {syntax, index, &used};
    }

    return {nullptr, SymbolIndex(), nullptr};
}

void Compilation::addExternInterfaceMethod(const SubroutineSymbol& method) {
    externInterfaceMethods.push_back(&method);
}

void Compilation::noteDefaultClocking(const Scope& scope, const Symbol& clocking,
                                      SourceRange range) {
    auto [it, inserted] = defaultClockingMap.emplace(&scope, &clocking);
    if (!inserted) {
        auto& diag = scope.addDiag(diag::MultipleDefaultClocking, range);
        diag.addNote(diag::NotePreviousDefinition, it->second->location);
    }
}

void Compilation::noteDefaultClocking(const ASTContext& context,
                                      const DefaultClockingReferenceSyntax& syntax) {
    auto name = syntax.name.valueText();
    auto range = syntax.name.range();
    auto sym = Lookup::unqualifiedAt(*context.scope, name, context.getLocation(), range);
    if (!sym)
        return;

    if (sym->kind != SymbolKind::ClockingBlock) {
        auto& diag = context.addDiag(diag::NotAClockingBlock, range);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, sym->location);
        return;
    }

    noteDefaultClocking(*context.scope, *sym, range);
}

const Symbol* Compilation::getDefaultClocking(const Scope& scope) const {
    auto curr = &scope;
    while (true) {
        if (auto it = defaultClockingMap.find(curr); it != defaultClockingMap.end())
            return it->second;

        curr = curr->asSymbol().getParentScope();
        if (!curr || curr->asSymbol().kind == SymbolKind::CompilationUnit)
            return nullptr;
    }
}

void Compilation::noteGlobalClocking(const Scope& scope, const Symbol& clocking,
                                     SourceRange range) {
    auto [it, inserted] = globalClockingMap.emplace(&scope, &clocking);
    if (!inserted) {
        auto& diag = scope.addDiag(diag::MultipleGlobalClocking, range);
        diag.addNote(diag::NotePreviousDefinition, it->second->location);
    }
}

const Symbol* Compilation::getGlobalClocking(const Scope& scope) const {
    auto curr = &scope;
    do {
        if (auto it = globalClockingMap.find(curr); it != globalClockingMap.end())
            return it->second;

        curr = curr->asSymbol().getHierarchicalParent();
    } while (curr);

    return nullptr;
}

void Compilation::noteDefaultDisable(const Scope& scope, const Expression& expr) {
    auto [it, inserted] = defaultDisableMap.emplace(&scope, &expr);
    if (!inserted) {
        auto& diag = scope.addDiag(diag::MultipleDefaultDisable, expr.sourceRange);
        diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange);
    }
}

void Compilation::noteNameConflict(const Symbol& symbol) {
    nameConflicts.push_back(&symbol);
}

const Expression* Compilation::getDefaultDisable(const Scope& scope) const {
    auto curr = &scope;
    while (true) {
        if (auto it = defaultDisableMap.find(curr); it != defaultDisableMap.end())
            return it->second;

        curr = curr->asSymbol().getParentScope();
        if (!curr || curr->asSymbol().kind == SymbolKind::CompilationUnit)
            return nullptr;
    }
}

void Compilation::noteExternModule(const Scope& scope, const ExternModuleDeclSyntax& syntax) {
    auto name = syntax.header->name.valueText();
    if (name.empty())
        return;

    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    auto [it, inserted] = externModuleMap.emplace(std::tuple(name, targetScope), &syntax);
    if (!inserted) {
        checkExternModMatch(scope, *syntax.header, *it->second->header,
                            diag::ExternDeclMismatchPrev);
        return;
    }

    if (auto udpIt = externUdpMap.find(std::tuple(name, targetScope));
        udpIt != externUdpMap.end()) {
        auto& diag = scope.addDiag(diag::Redefinition, syntax.header->name.location());
        diag << name;
        diag.addNote(diag::NotePreviousDefinition, udpIt->second->name.location());
    }
}

const ExternModuleDeclSyntax* Compilation::getExternModule(std::string_view name,
                                                           const Scope& scope) const {
    const Scope* searchScope = &scope;
    do {
        auto it = externModuleMap.find(std::make_tuple(name, searchScope));
        if (it != externModuleMap.end())
            return it->second;

        searchScope = searchScope->asSymbol().getParentScope();
    } while (searchScope);

    return nullptr;
}

bool Compilation::errorIfMissingExternModule(std::string_view name, const Scope& scope,
                                             SourceRange sourceRange) {
    auto decl = getExternModule(name, scope);
    if (!decl)
        return false;

    auto& diag = scope.addDiag(diag::MissingExternModuleImpl, decl->header->name.range());
    diag << decl->header->moduleKeyword.valueText();
    diag << name;
    diag.addNote(diag::NoteReferencedHere, sourceRange);
    return true;
}

void Compilation::noteExternPrimitive(const Scope& scope, const ExternUdpDeclSyntax& syntax) {
    auto name = syntax.name.valueText();
    if (name.empty())
        return;

    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    auto [it, inserted] = externUdpMap.emplace(std::tuple(name, targetScope), &syntax);
    if (!inserted) {
        checkExternUdpMatch(scope, *syntax.portList, *it->second->portList, name,
                            diag::ExternDeclMismatchPrev);
        return;
    }

    if (auto modIt = externModuleMap.find(std::tuple(name, targetScope));
        modIt != externModuleMap.end()) {
        auto& diag = scope.addDiag(diag::Redefinition, syntax.name.location());
        diag << name;
        diag.addNote(diag::NotePreviousDefinition, modIt->second->header->name.location());
    }
}

const ExternUdpDeclSyntax* Compilation::getExternPrimitive(std::string_view name,
                                                           const Scope& scope) const {
    const Scope* searchScope = &scope;
    do {
        auto it = externUdpMap.find(std::make_tuple(name, searchScope));
        if (it != externUdpMap.end())
            return it->second;

        searchScope = searchScope->asSymbol().getParentScope();
    } while (searchScope);

    return nullptr;
}

bool Compilation::errorIfMissingExternPrimitive(std::string_view name, const Scope& scope,
                                                SourceRange sourceRange) {
    auto decl = getExternPrimitive(name, scope);
    if (!decl)
        return false;

    auto& diag = scope.addDiag(diag::MissingExternModuleImpl, decl->name.range());
    diag << "primitive"sv;
    diag << name;
    diag.addNote(diag::NoteReferencedHere, sourceRange);
    return true;
}

void Compilation::noteReference(const SyntaxNode& node, bool isLValue) {
    auto [it, inserted] = referenceStatusMap.emplace(&node, std::pair{!isLValue, isLValue});
    if (!inserted) {
        it->second.first |= !isLValue;
        it->second.second |= isLValue;
    }
}

void Compilation::noteReference(const Symbol& symbol, bool isLValue) {
    if (auto syntax = symbol.getSyntax())
        noteReference(*syntax, isLValue);
}

std::pair<bool, bool> Compilation::isReferenced(const SyntaxNode& node) const {
    auto it = referenceStatusMap.find(&node);
    if (it == referenceStatusMap.end())
        return {false, false};

    return it->second;
}

const NameSyntax& Compilation::parseName(std::string_view name) {
    Diagnostics localDiags;
    auto& result = tryParseName(name, localDiags);

    if (!localDiags.empty()) {
        SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
        localDiags.sort(sourceMan);
        SLANG_THROW(std::runtime_error(DiagnosticEngine::reportAll(sourceMan, localDiags)));
    }

    return result;
}

const NameSyntax& Compilation::tryParseName(std::string_view name, Diagnostics& localDiags) {
    SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
    Preprocessor preprocessor(sourceMan, *this, localDiags);
    preprocessor.pushSource(name);

    Parser parser(preprocessor);
    return parser.parseName();
}

CompilationUnitSymbol& Compilation::createScriptScope() {
    auto unit = emplace<CompilationUnitSymbol>(*this);
    root->addMember(*unit);
    return *unit;
}

const Diagnostics& Compilation::getParseDiagnostics() {
    if (cachedParseDiagnostics)
        return *cachedParseDiagnostics;

    cachedParseDiagnostics.emplace();
    for (const auto& tree : syntaxTrees)
        cachedParseDiagnostics->append_range(tree->diagnostics());

    if (sourceManager)
        cachedParseDiagnostics->sort(*sourceManager);
    return *cachedParseDiagnostics;
}

const Diagnostics& Compilation::getSemanticDiagnostics() {
    if (cachedSemanticDiagnostics)
        return *cachedSemanticDiagnostics;

    // If we haven't already done so, touch every symbol, scope, statement,
    // and expression tree so that we can be sure we have all the diagnostics.
    uint32_t errorLimit = options.errorLimit == 0 ? UINT32_MAX : options.errorLimit;
    DiagnosticVisitor elabVisitor(*this, numErrors, errorLimit);
    getRoot().visit(elabVisitor);

    if (!elabVisitor.finishedEarly()) {
        elabVisitor.finalize();

        // Note for the following checks here: anything that depends on a list
        // stored in the compilation object should think carefully about taking
        // a copy of that list first before iterating over it, because your check
        // might trigger additional action that ends up adding to that list,
        // causing undefined behavior.

        // Check all DPI methods for correctness.
        if (!dpiExports.empty() || !elabVisitor.dpiImports.empty())
            checkDPIMethods(elabVisitor.dpiImports);

        // Check extern interface methods for correctness.
        if (!externInterfaceMethods.empty()) {
            auto methods = externInterfaceMethods;
            for (auto method : methods)
                method->connectExternInterfacePrototype();
        }

        if (!elabVisitor.externIfaceProtos.empty())
            checkExternIfaceMethods(elabVisitor.externIfaceProtos);

        if (!elabVisitor.modportsWithExports.empty())
            checkModportExports(elabVisitor.modportsWithExports);

        // Double check any bind directives for correctness. These were already
        // resolve prior to full elaboration but their diagnostics were not
        // issued so we need to check again.
        for (auto [directive, scope] : bindDirectives) {
            SmallVector<const Symbol*> instTargets;
            const DefinitionSymbol* defTarget = nullptr;
            resolveBindTargets(*directive, *scope, instTargets, &defTarget);
            checkBindTargetParams(*directive, *scope, instTargets, defTarget);
        }

        // Report any lingering name conflicts.
        if (!nameConflicts.empty()) {
            auto conflicts = nameConflicts;
            for (auto symbol : conflicts) {
                auto scope = symbol->getParentScope();
                SLANG_ASSERT(scope);
                scope->handleNameConflict(*symbol);
            }
        }

        // Report on unused out-of-block definitions. These are always a real error.
        if (!outOfBlockDecls.empty()) {
            auto decls = outOfBlockDecls;
            for (auto& [key, val] : decls) {
                auto& [syntax, name, index, used] = val;
                if (!used) {
                    auto& [className, declName, scope] = key;
                    auto classRange = name->left->sourceRange();
                    auto sym = Lookup::unqualifiedAt(*scope, className,
                                                     LookupLocation(scope, uint32_t(index)),
                                                     classRange);

                    if (sym && !declName.empty() && !className.empty()) {
                        if (sym->kind == SymbolKind::ClassType ||
                            sym->kind == SymbolKind::GenericClassDef) {
                            auto& diag = scope->addDiag(diag::NoDeclInClass, name->sourceRange());
                            diag << declName << className;
                        }
                        else {
                            auto& diag = scope->addDiag(diag::NotAClass, classRange);
                            diag << className;
                        }
                    }
                }
            }
        }

        if (!hasFlag(CompilationFlags::AllowTopLevelIfacePorts)) {
            // Top level instances cannot have interface or ref ports.
            for (auto inst : getRoot().topInstances) {
                for (auto port : inst->body.getPortList()) {
                    if (port->kind == SymbolKind::InterfacePort) {
                        inst->body.addDiag(diag::TopModuleIfacePort, port->location)
                            << inst->name << port->name;
                        break;
                    }
                    else {
                        ArgumentDirection dir;
                        if (port->kind == SymbolKind::MultiPort)
                            dir = port->as<MultiPortSymbol>().direction;
                        else
                            dir = port->as<PortSymbol>().direction;

                        if (dir == ArgumentDirection::Ref) {
                            if (port->name.empty()) {
                                inst->body.addDiag(diag::TopModuleUnnamedRefPort, port->location)
                                    << inst->name;
                            }
                            else {
                                inst->body.addDiag(diag::TopModuleRefPort, port->location)
                                    << inst->name << port->name;
                            }
                        }
                    }
                }
            }
        }

        if (!hasFlag(CompilationFlags::SuppressUnused)) {
            // Report on unused definitions.
            for (auto def : unreferencedDefs) {
                // If this is an interface, it may have been referenced in a port.
                if (elabVisitor.usedIfacePorts.find(def) != elabVisitor.usedIfacePorts.end())
                    continue;

                auto hasUnusedAttrib = [&] {
                    for (auto attr : getAttributes(*def)) {
                        if (attr->name == "unused"sv || attr->name == "maybe_unused"sv)
                            return attr->getValue().isTrue();
                    }
                    return false;
                };

                if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib())
                    def->getParentScope()->addDiag(diag::UnusedDefinition, def->location)
                        << def->getKindString();
            }

            if (!elabVisitor.hierarchyProblem && numErrors == 0) {
                PostElabVisitor postElabVisitor(*this);
                getRoot().visit(postElabVisitor);
            }
        }
    }

    Diagnostics results;
    for (auto& [key, diagList] : diagMap) {
        // If the location is NoLocation, just issue each diagnostic.
        if (std::get<1>(key) == SourceLocation::NoLocation) {
            for (auto& diag : diagList)
                results.emplace_back(diag);
            continue;
        }

        // Try to find a diagnostic in an instance that isn't at the top-level
        // (printing such a path seems silly).
        const Diagnostic* found = nullptr;
        const Symbol* inst = nullptr;
        size_t count = 0;
        bool differingArgs = false;

        for (auto& diag : diagList) {
            if (found && *found != diag) {
                differingArgs = true;
                break;
            }

            auto symbol = diag.symbol;
            while (symbol && symbol->kind != SymbolKind::InstanceBody) {
                const Scope* scope;
                if (symbol->kind == SymbolKind::CheckerInstanceBody) {
                    auto& checkerBody = symbol->as<CheckerInstanceBodySymbol>();
                    SLANG_ASSERT(checkerBody.parentInstance);
                    scope = checkerBody.parentInstance->getParentScope();

                    // Add an expansion note to the diagnostic since
                    // we won't have added it yet for the checker.
                    if (!checkerBody.isUninstantiated) {
                        diag.addNote(diag::NoteWhileExpanding, checkerBody.parentInstance->location)
                            << "checker"sv << checkerBody.checker.name;
                    }
                }
                else {
                    scope = symbol->getParentScope();
                }

                symbol = scope ? &scope->asSymbol() : nullptr;
            }

            if (!symbol)
                continue;

            auto parent = symbol->as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(parent);

            count++;
            if (auto scope = parent->getParentScope()) {
                auto& sym = scope->asSymbol();
                if (sym.kind != SymbolKind::Root && sym.kind != SymbolKind::CompilationUnit) {
                    found = &diag;
                    inst = parent;
                }
            }
        }

        if (!differingArgs && found &&
            elabVisitor.instanceCount[&inst->as<InstanceSymbol>().getDefinition()] > count) {
            // The diagnostic is present only in some instances, so include the coalescing
            // information to point the user towards the right ones.
            Diagnostic diag = *found;
            diag.symbol = inst;
            diag.coalesceCount = count;
            results.emplace_back(std::move(diag));
        }
        else {
            // Otherwise no coalescing. If we had differing arguments then set each
            // diagnostic's coalesce count to 1 (as opposed to letting it stay nullopt)
            // so that we get the instance path to it printed automatically.
            auto it = diagList.begin();
            SLANG_ASSERT(it != diagList.end());

            {
                Diagnostic d = *it;
                if (differingArgs)
                    d.coalesceCount = 1;
                results.emplace_back(std::move(d));
            }

            for (++it; it != diagList.end(); ++it) {
                Diagnostic d = *it;
                if (d != results.back()) {
                    if (differingArgs)
                        d.coalesceCount = 1;
                    results.emplace_back(std::move(d));
                }
            }
        }
    }

    if (sourceManager)
        results.sort(*sourceManager);

    cachedSemanticDiagnostics.emplace(std::move(results));
    return *cachedSemanticDiagnostics;
}

const Diagnostics& Compilation::getAllDiagnostics() {
    if (cachedAllDiagnostics)
        return *cachedAllDiagnostics;

    cachedAllDiagnostics.emplace();
    cachedAllDiagnostics->append_range(getParseDiagnostics());
    cachedAllDiagnostics->append_range(getSemanticDiagnostics());

    if (sourceManager)
        cachedAllDiagnostics->sort(*sourceManager);
    return *cachedAllDiagnostics;
}

void Compilation::addDiagnostics(const Diagnostics& diagnostics) {
    for (auto& diag : diagnostics)
        addDiag(diag);
}

Diagnostic& Compilation::addDiag(Diagnostic diag) {
    auto isSuppressed = [](const Symbol* symbol) {
        while (symbol) {
            if (symbol->kind == SymbolKind::GenerateBlock)
                return symbol->as<GenerateBlockSymbol>().isUninstantiated;

            auto scope = symbol->getParentScope();
            symbol = scope ? &scope->asSymbol() : nullptr;
        }
        return false;
    };

    // Filter out diagnostics that came from inside an uninstantiated generate block.
    SLANG_ASSERT(diag.symbol);
    SLANG_ASSERT(diag.location);
    if (isSuppressed(diag.symbol)) {
        tempDiag = std::move(diag);
        return tempDiag;
    }

    // Coalesce diagnostics that are at the same source location and have the same code.
    if (auto it = diagMap.find({diag.code, diag.location}); it != diagMap.end()) {
        auto& diagList = it->second;
        diagList.emplace_back(std::move(diag));
        return diagList.back();
    }

    if (diag.isError())
        numErrors++;

    auto key = std::make_tuple(diag.code, diag.location);
    std::vector<Diagnostic> newEntry;
    newEntry.emplace_back(std::move(diag));

    auto [it, inserted] = diagMap.emplace(key, std::move(newEntry));
    return it->second.back();
}

AssertionInstanceDetails* Compilation::allocAssertionDetails() {
    return assertionDetailsAllocator.emplace();
}

ConfigBlockSymbol* Compilation::allocConfigBlock(std::string_view name, SourceLocation loc) {
    return configBlockAllocator.emplace(*this, name, loc);
}

const ImplicitTypeSyntax& Compilation::createEmptyTypeSyntax(SourceLocation loc) {
    return *emplace<ImplicitTypeSyntax>(Token(), nullptr,
                                        Token(*this, TokenKind::Placeholder, {}, {}, loc));
}

void Compilation::forceElaborate(const Symbol& symbol) {
    DiagnosticVisitor visitor(*this, numErrors,
                              options.errorLimit == 0 ? UINT32_MAX : options.errorLimit);
    symbol.visit(visitor);
}

const Type& Compilation::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? *errorType : *it->second;
}

const Type& Compilation::getType(const DataTypeSyntax& node, const ASTContext& context,
                                 const Type* typedefTarget) {
    return Type::fromSyntax(*this, node, context, typedefTarget);
}

const Type& Compilation::getType(const Type& elementType,
                                 const SyntaxList<VariableDimensionSyntax>& dimensions,
                                 const ASTContext& context) {
    return Type::fromSyntax(*this, elementType, dimensions, context);
}

const Type& Compilation::getType(bitwidth_t width, bitmask<IntegralFlags> flags) {
    SLANG_ASSERT(width > 0 && width <= SVInt::MAX_BITS);
    uint32_t key = width;
    key |= uint32_t(flags.bits()) << SVInt::BITWIDTH_BITS;
    auto it = vectorTypeCache.find(key);
    if (it != vectorTypeCache.end())
        return *it->second;

    auto type = emplace<PackedArrayType>(getScalarType(flags), ConstantRange{int32_t(width - 1), 0},
                                         width);
    vectorTypeCache.emplace_hint(it, key, type);
    return *type;
}

const Type& Compilation::getScalarType(bitmask<IntegralFlags> flags) {
    Type* ptr = scalarTypeTable[flags.bits() & 0x7];
    SLANG_ASSERT(ptr);
    return *ptr;
}

const NetType& Compilation::getNetType(TokenKind kind) const {
    auto it = knownNetTypes.find(kind);
    return it == knownNetTypes.end() ? *knownNetTypes.find(TokenKind::Unknown)->second
                                     : *it->second;
}

const Type& Compilation::getUnsignedIntType() {
    return getType(32, IntegralFlags::Unsigned | IntegralFlags::TwoState);
}

const Type& Compilation::getNullType() {
    return getType(SyntaxKind::NullLiteralExpression);
}

const Type& Compilation::getUnboundedType() {
    return getType(SyntaxKind::WildcardLiteralExpression);
}

const Type& Compilation::getTypeRefType() {
    return getType(SyntaxKind::TypeReference);
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
        index = importData.add({&import});
}

std::span<const WildcardImportSymbol*> Compilation::queryImports(Scope::ImportDataIndex index) {
    if (index == Scope::ImportDataIndex::Invalid)
        return {};
    return importData[index];
}

void Compilation::parseParamOverrides(
    flat_hash_map<std::string_view, const ConstantValue*>& results) {
    if (options.paramOverrides.empty())
        return;

    ScriptSession session;
    for (auto& opt : options.paramOverrides) {
        // Strings must be of the form <name>=<value>
        size_t index = opt.find('=');
        if (index != std::string::npos) {
            // We found the equals sign, so split out the name and parse that.
            // For now, the name must always be a simple identifier.
            Diagnostics localDiags;
            std::string_view optView = opt;
            std::string_view name = optView.substr(0, index);
            if (tryParseName(name, localDiags).kind == SyntaxKind::IdentifierName &&
                localDiags.empty()) {

                // The name is good, evaluate the value string. Using the ScriptSession
                // here is a little bit lazy but oh well, this executes almost never
                // compared to everything else during compilation.
                std::string_view value = optView.substr(index + 1);
                ConstantValue cv = session.eval(value);
                if (cv) {
                    // Success, store in the map so we can apply the value later.
                    results.emplace(name, allocConstant(std::move(cv)));
                    continue;
                }
            }
        }

        root->addDiag(diag::InvalidParamOverrideOpt, SourceLocation::NoLocation) << opt;
    }
}

static bool checkSignaturesMatch(const SubroutineSymbol& a, const SubroutineSymbol& b) {
    if (a.subroutineKind != b.subroutineKind || a.flags != b.flags)
        return false;

    if (!a.getReturnType().isEquivalent(b.getReturnType()))
        return false;

    auto aargs = a.getArguments();
    auto bargs = b.getArguments();
    if (aargs.size() != bargs.size())
        return false;

    for (auto ai = aargs.begin(), bi = bargs.begin(); ai != aargs.end(); ai++, bi++) {
        auto aa = *ai;
        auto bb = *bi;
        if (!aa->getType().isEquivalent(bb->getType()))
            return false;
        if (aa->direction != bb->direction)
            return false;
    }

    return true;
}

void Compilation::checkDPIMethods(std::span<const SubroutineSymbol* const> dpiImports) {
    auto getCId = [&](const Scope& scope, Token cid, Token name) {
        std::string_view text = cid ? cid.valueText() : name.valueText();
        if (!text.empty()) {
            auto tail = text.substr(1);
            if (!isValidCIdChar(text[0]) || isDecimalDigit(text[0]) ||
                std::ranges::any_of(tail, [](char c) { return !isValidCIdChar(c); })) {
                scope.addDiag(diag::InvalidDPICIdentifier, cid ? cid.range() : name.range())
                    << text;
                return std::string_view();
            }
        }
        return text;
    };

    flat_hash_map<std::string_view, const SubroutineSymbol*> nameMap;
    for (auto sub : dpiImports) {
        auto syntax = sub->getSyntax();
        SLANG_ASSERT(syntax);

        auto scope = sub->getParentScope();
        SLANG_ASSERT(scope);

        auto& dis = syntax->as<DPIImportSyntax>();
        std::string_view cId = getCId(*scope, dis.c_identifier, dis.method->name->getLastToken());
        if (cId.empty())
            continue;

        auto [it, inserted] = nameMap.emplace(cId, sub);
        if (!inserted) {
            if (!checkSignaturesMatch(*sub, *it->second)) {
                auto& diag = scope->addDiag(diag::DPISignatureMismatch, sub->location);
                diag << cId;
                diag.addNote(diag::NotePreviousDefinition, it->second->location);
            }
        }
    }

    flat_hash_map<std::tuple<std::string_view, const Scope*>, const DPIExportSyntax*>
        exportsByScope;
    flat_hash_map<const SubroutineSymbol*, const DPIExportSyntax*> previousExports;
    auto exports = dpiExports;
    for (auto [syntax, scope] : exports) {
        if (syntax->specString.valueText() == "DPI")
            scope->addDiag(diag::DPISpecDisallowed, syntax->specString.range());

        auto name = syntax->name.valueText();
        auto symbol = Lookup::unqualifiedAt(*scope, name, LookupLocation::max,
                                            syntax->name.range());
        if (!symbol)
            continue;

        if (symbol->kind != SymbolKind::Subroutine) {
            auto& diag = scope->addDiag(diag::NotASubroutine, syntax->name.range()) << name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            continue;
        }

        // This check is a little verbose because we're avoiding issuing an error if the
        // functionOrTask keyword is invalid, i.e. not 'function' or 'task'.
        auto& sub = symbol->as<SubroutineSymbol>();
        if ((sub.subroutineKind == SubroutineKind::Function &&
             syntax->functionOrTask.kind == TokenKind::TaskKeyword) ||
            (sub.subroutineKind == SubroutineKind::Task &&
             syntax->functionOrTask.kind == TokenKind::FunctionKeyword)) {
            auto& diag = scope->addDiag(diag::DPIExportKindMismatch,
                                        syntax->functionOrTask.range());
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            continue;
        }

        if (sub.getParentScope() != scope) {
            auto& diag = scope->addDiag(diag::DPIExportDifferentScope, syntax->name.range());
            diag.addNote(diag::NoteDeclarationHere, sub.location);
            continue;
        }

        if (sub.flags.has(MethodFlags::DPIImport)) {
            auto& diag = scope->addDiag(diag::DPIExportImportedFunc, syntax->name.range());
            diag.addNote(diag::NoteDeclarationHere, sub.location);
            continue;
        }

        auto& retType = sub.getReturnType();
        if (!retType.isValidForDPIReturn() && !retType.isError()) {
            auto& diag = scope->addDiag(diag::InvalidDPIReturnType, sub.location);
            diag << retType;
            diag.addNote(diag::NoteDeclarationHere, syntax->name.location());
            continue;
        }

        for (auto arg : sub.getArguments()) {
            if (arg->direction == ArgumentDirection::Ref)
                scope->addDiag(diag::DPIRefArg, arg->location);

            auto& type = arg->getType();
            if (!type.isValidForDPIArg() && !type.isError()) {
                auto& diag = scope->addDiag(diag::InvalidDPIArgType, arg->location);
                diag << type;
                diag.addNote(diag::NoteDeclarationHere, syntax->name.location());
                continue;
            }
        }

        {
            auto [it, inserted] = previousExports.emplace(&sub, syntax);
            if (!inserted) {
                auto& diag = scope->addDiag(diag::DPIExportDuplicate, syntax->name.range())
                             << sub.name;
                diag.addNote(diag::NotePreviousDefinition, it->second->name.location());
                continue;
            }
        }

        std::string_view cId = getCId(*scope, syntax->c_identifier, syntax->name);
        if (!cId.empty()) {
            {
                auto [it, inserted] = nameMap.emplace(cId, &sub);
                if (!inserted) {
                    if (!checkSignaturesMatch(sub, *it->second)) {
                        auto& diag = scope->addDiag(diag::DPISignatureMismatch,
                                                    syntax->name.range());
                        diag << cId;
                        diag.addNote(diag::NotePreviousDefinition, it->second->location);
                    }
                }
            }
            {
                auto [it, inserted] = exportsByScope.emplace(std::make_tuple(cId, scope), syntax);
                if (!inserted) {
                    auto& diag = scope->addDiag(diag::DPIExportDuplicateCId, syntax->name.range());
                    diag << cId;
                    diag.addNote(diag::NotePreviousDefinition, it->second->name.location());
                }
            }
        }
    }
}

void Compilation::checkExternIfaceMethods(std::span<const MethodPrototypeSymbol* const> protos) {
    for (auto proto : protos) {
        if (!proto->getFirstExternImpl() && !proto->flags.has(MethodFlags::ForkJoin)) {
            auto scope = proto->getParentScope();
            SLANG_ASSERT(scope);

            auto& parent = scope->asSymbol();
            if (!parent.name.empty() && !proto->name.empty()) {
                auto& diag = scope->addDiag(diag::MissingExternImpl, proto->location);
                diag << (proto->subroutineKind == SubroutineKind::Function ? "function"sv
                                                                           : "task"sv);
                diag << parent.name << proto->name;
            }
        }
    }
}

void Compilation::checkModportExports(
    std::span<const std::pair<const InterfacePortSymbol*, const ModportSymbol*>> modports) {

    for (auto [port, modport] : modports) {
        auto def = port->getDeclaringDefinition();
        SLANG_ASSERT(def);

        for (auto& method : modport->membersOfType<MethodPrototypeSymbol>()) {
            if (method.flags.has(MethodFlags::ModportExport)) {
                bool found = false;
                auto impl = method.getFirstExternImpl();
                while (impl) {
                    if (impl->impl->getDeclaringDefinition() == def) {
                        found = true;
                        break;
                    }
                    impl = impl->getNextImpl();
                }

                if (!found) {
                    auto& diag = port->getParentScope()->addDiag(diag::MissingExportImpl,
                                                                 port->location);
                    diag << method.name << def->name;
                    diag.addNote(diag::NoteDeclarationHere, method.location);
                }
            }
        }
    }
}

void Compilation::checkElemTimeScale(std::optional<TimeScale> timeScale, SourceRange sourceRange) {
    if (timeScale) {
        if (anyElemsWithTimescales)
            return;

        anyElemsWithTimescales = true;
        for (auto& def : definitionMemory) {
            auto& syntax = def->getSyntax()->as<ModuleDeclarationSyntax>();
            checkElemTimeScale(def->timeScale, syntax.header->name.range());
        }

        for (auto [name, package] : packageMap) {
            if (auto syntax = package->getSyntax()) {
                checkElemTimeScale(package->timeScale,
                                   syntax->as<ModuleDeclarationSyntax>().header->name.range());
            }
        }
    }
    else if (anyElemsWithTimescales) {
        root->addDiag(diag::MissingTimeScale, sourceRange);
    }
}

void Compilation::resolveBindTargets(const BindDirectiveSyntax& syntax, const Scope& scope,
                                     SmallVector<const Symbol*>& instTargets,
                                     const DefinitionSymbol** defTarget) {
    auto checkValidTarget = [&](const Symbol& symbol, const SyntaxNode& nameSyntax) {
        if (symbol.kind == SymbolKind::Instance) {
            auto defKind = symbol.as<InstanceSymbol>().getDefinition().definitionKind;
            if (defKind == DefinitionKind::Module || defKind == DefinitionKind::Interface)
                return true;
        }

        auto& diag = scope.addDiag(diag::InvalidBindTarget, nameSyntax.sourceRange());
        diag << symbol.name;
        diag.addNote(diag::NoteDeclarationHere, symbol.location);
        return false;
    };

    // If an instance list is given, then the target name must be a definition name.
    // Otherwise, the target name can be either an instance name or a definition name,
    // preferencing the instance if found.
    ASTContext context(scope, LookupLocation::max);
    bitmask<LookupFlags> flags = LookupFlags::ForceHierarchical |
                                 LookupFlags::DisallowWildcardImport | LookupFlags::NoSelectors;

    if (syntax.targetInstances) {
        if (syntax.target->kind != SyntaxKind::IdentifierName)
            return;

        Token name = syntax.target->as<IdentifierNameSyntax>().identifier;
        auto targetDef = getDefinition(name.valueText(), scope);
        if (!targetDef) {
            if (!errorIfMissingExternModule(name.valueText(), scope, name.range()))
                scope.addDiag(diag::UnknownModule, name.range()) << name.valueText();
            return;
        }

        for (auto inst : syntax.targetInstances->targets) {
            LookupResult result;
            Lookup::name(*inst, context, flags, result);
            result.reportDiags(context);

            if (result.found) {
                if (checkValidTarget(*result.found, *inst)) {
                    if (&result.found->as<InstanceSymbol>().getDefinition() != targetDef) {
                        auto& diag = scope.addDiag(diag::WrongBindTargetDef, inst->sourceRange());
                        diag << result.found->name << targetDef->name;
                        diag << syntax.target->sourceRange();
                        diag.addNote(diag::NoteDeclarationHere, result.found->location);
                    }
                    instTargets.push_back(result.found);
                }
            }
        }
    }
    else {
        LookupResult result;
        Lookup::name(*syntax.target, context, flags, result);

        if (result.found) {
            if (checkValidTarget(*result.found, *syntax.target))
                instTargets.push_back(result.found);
        }
        else {
            // If we didn't find the name as an instance, try as a definition.
            if (syntax.target->kind == SyntaxKind::IdentifierName) {
                Token name = syntax.target->as<IdentifierNameSyntax>().identifier;
                if (auto def = getDefinition(name.valueText(), scope)) {
                    *defTarget = def;
                    return;
                }

                if (errorIfMissingExternModule(name.valueText(), scope, name.range()))
                    return;
            }

            // If no name and no definition, report an error.
            result.reportDiags(context);
        }
    }
}

void Compilation::checkBindTargetParams(const syntax::BindDirectiveSyntax& syntax,
                                        const Scope& scope,
                                        std::span<const Symbol* const> instTargets,
                                        const DefinitionSymbol* defTarget) {
    // This method checks the following rule from the LRM:
    //    User-defined type names that are used to override type parameters must be
    //    visible and matching in both the scope containing the bind statement and in
    //    the target scope.
    auto doCheck = [&](const InstanceBodySymbol& container) {
        if (syntax.instantiation->kind == SyntaxKind::CheckerInstantiation)
            return;

        for (auto instSyntax : syntax.instantiation->as<HierarchyInstantiationSyntax>().instances) {
            if (!instSyntax->decl)
                continue;

            auto sym = container.find(instSyntax->decl->name.valueText());
            if (!sym || sym->kind != SymbolKind::Instance || sym->getSyntax() != instSyntax)
                continue;

            auto& inst = sym->as<InstanceSymbol>();
            for (auto param : inst.body.parameters) {
                if (param->symbol.kind == SymbolKind::TypeParameter) {
                    auto& typeParam = param->symbol.as<TypeParameterSymbol>();
                    auto& type = typeParam.targetType.getType();
                    if (typeParam.isOverridden() && type.isAlias() && !type.name.empty()) {
                        // This is the case we need to check; the resolved type is
                        // a named type alias, so we need to also resolve it in the bind
                        // directive scope and make sure they match.
                        auto result = Lookup::unqualified(scope, type.name, LookupFlags::Type);
                        if (!result || !result->isType()) {
                            auto ts = typeParam.getDeclaredType()->getTypeSyntax();
                            SLANG_ASSERT(ts);
                            scope.addDiag(diag::BindTypeParamNotFound, ts->sourceRange())
                                << typeParam.name << type;
                        }
                        else if (!result->as<Type>().isMatching(type)) {
                            auto ts = typeParam.getDeclaredType()->getTypeSyntax();
                            SLANG_ASSERT(ts);
                            scope.addDiag(diag::BindTypeParamMismatch, ts->sourceRange())
                                << typeParam.name << result->as<Type>() << type;
                        }
                    }
                }
            }
        }
    };

    for (auto target : instTargets)
        doCheck(target->as<InstanceSymbol>().body);

    if (defTarget) {
        auto it = instancesWithDefBinds.find(defTarget);
        if (it != instancesWithDefBinds.end()) {
            for (auto target : it->second)
                doCheck(target->as<InstanceBodySymbol>());
        }
    }
}

void Compilation::resolveDefParamsAndBinds() {
    TimeTraceScope timeScope("resolveDefParamsAndBinds"sv, ""sv);

    struct OverrideEntry {
        InstancePath path;
        const SyntaxNode* targetSyntax = nullptr;
        const SyntaxNode* defparamSyntax = nullptr;
        ConstantValue value;
        std::string pathStr;
    };
    SmallVector<OverrideEntry, 4> overrides;

    struct BindEntry {
        InstancePath path;
        const BindDirectiveSyntax* syntax = nullptr;
        const ModuleDeclarationSyntax* definitionTarget = nullptr;
    };
    SmallVector<BindEntry> binds;

    auto getNodeFor = [](const InstancePath& path, Compilation& c) {
        HierarchyOverrideNode* node = &c.hierarchyOverrides;
        for (auto& entry : path.entries)
            node = &node->childrenBySyntax[entry];
        return node;
    };

    auto copyStateInto = [&](Compilation& c, bool isFinal) {
        for (auto& entry : overrides) {
            if (!entry.targetSyntax)
                continue;

            SLANG_ASSERT(entry.defparamSyntax);

            auto node = getNodeFor(entry.path, c);
            auto [it, inserted] = node->overridesBySyntax.emplace(
                entry.targetSyntax, std::pair{entry.value, entry.defparamSyntax});

            if (!inserted && isFinal) {
                SLANG_ASSERT(it->second.second);
                auto& diag = c.root->addDiag(diag::DuplicateDefparam,
                                             entry.defparamSyntax->sourceRange());
                diag.addNote(diag::NotePreviousDefinition, it->second.second->sourceRange());
            }
        }

        for (auto& entry : binds) {
            if (entry.definitionTarget) {
                auto it = c.definitionFromSyntax.find(entry.definitionTarget);
                SLANG_ASSERT(it != c.definitionFromSyntax.end());
                it->second->bindDirectives.push_back(entry.syntax);
            }
            else {
                auto node = getNodeFor(entry.path, c);
                node->binds.push_back(entry.syntax);
            }
        }
    };

    auto cloneInto = [&](Compilation& c) {
        c.options = options;
        for (auto& tree : syntaxTrees)
            c.addSyntaxTree(tree);

        copyStateInto(c, false);
    };

    auto saveState = [&](DefParamVisitor& visitor, Compilation& c) {
        overrides.clear();
        for (auto defparam : visitor.found) {
            auto target = defparam->getTarget();
            if (!target) {
                overrides.emplace_back();
            }
            else {
                std::string path;
                target->getHierarchicalPath(path);

                overrides.push_back({InstancePath(*target), target->getSyntax(),
                                     defparam->getSyntax(), defparam->getValue(), std::move(path)});
            }
        }

        binds.clear();
        for (auto [syntax, scope] : c.bindDirectives) {
            SmallVector<const Symbol*> instTargets;
            const DefinitionSymbol* defTarget = nullptr;
            c.resolveBindTargets(*syntax, *scope, instTargets, &defTarget);

            for (auto target : instTargets)
                binds.emplace_back(BindEntry{InstancePath(*target), syntax});

            if (defTarget) {
                auto& modSyntax = defTarget->getSyntax()->as<ModuleDeclarationSyntax>();
                binds.emplace_back(BindEntry{{}, syntax, &modSyntax});
            }
        }
    };

    auto checkProblem = [&](const DefParamVisitor& visitor) {
        if (visitor.hierarchyProblem) {
            auto& diag = root->addDiag(diag::MaxInstanceDepthExceeded,
                                       visitor.hierarchyProblem->location);
            diag << visitor.hierarchyProblem->getDefinition().getKindString();
            diag << options.maxInstanceDepth;
            return true;
        }
        return false;
    };

    // [23.10.4.1] gives an algorithm for elaboration in the face of defparams.
    // Specifically, we need to resolve all possible defparams at one "level" of
    // hierarchy before moving on to a deeper level, where a "level" in this case
    // is each successive set of nested generate blocks.
    size_t generateLevel = 0;
    size_t numBlocksSeen = 0;
    size_t numBindsSeen = 0;
    while (true) {
        // Traverse the design and find all defparams and their values.
        // defparam resolution happens in a cloned compilation unit because we will be
        // constantly mucking with parameter values in ways that can change the actual
        // hierarchy that gets instantiated. Cloning lets us do that in an isolated context
        // and throw that work away once we know the final parameter values.
        Compilation initialClone;
        cloneInto(initialClone);

        DefParamVisitor initialVisitor(options.maxInstanceDepth, generateLevel);
        initialClone.getRoot(/* skipDefParamsAndBinds */ true).visit(initialVisitor);
        saveState(initialVisitor, initialClone);
        if (checkProblem(initialVisitor))
            return;

        // If we have found more binds, do another visit to let them be applied
        // and potentially add blocks and defparams to our set for this level.
        if (initialClone.bindDirectives.size() > numBindsSeen) {
            numBindsSeen = initialClone.bindDirectives.size();
            continue;
        }

        // defparams can change the value of parameters, further affecting the value of
        // other defparams elsewhere in the design. This means we need to iterate,
        // reevaluating defparams until they all settle to a stable value or until we
        // give up due to the potential of cyclical references.
        bool allSame = true;
        for (uint32_t i = 0; i < options.maxDefParamSteps; i++) {
            Compilation c;
            cloneInto(c);

            DefParamVisitor v(options.maxInstanceDepth, generateLevel);
            c.getRoot(/* skipDefParamsAndBinds */ true).visit(v);
            if (checkProblem(v))
                return;

            // We're only done if we have the same set of defparams with the same set of values.
            allSame = true;
            SLANG_ASSERT(v.found.size() == overrides.size());
            for (size_t j = 0; j < v.found.size(); j++) {
                // Check that the defparam resolved to the same target we saw previously.
                // The spec declares it to be an error if a defparam target changes based
                // on elaboration of other defparam values.
                const SyntaxNode* targetNode = nullptr;
                auto target = v.found[j]->getTarget();
                if (target)
                    targetNode = target->getSyntax();

                auto getRange = [&] {
                    auto syntax = v.found[j]->getSyntax();
                    SLANG_ASSERT(syntax);
                    return syntax->sourceRange();
                };

                auto& prevEntry = overrides[j];
                if (prevEntry.targetSyntax && targetNode && prevEntry.targetSyntax != targetNode) {
                    std::string path;
                    target->getHierarchicalPath(path);

                    auto& diag = root->addDiag(diag::DefParamTargetChange, getRange());
                    diag << prevEntry.pathStr;
                    diag << path;
                    return;
                }

                if (prevEntry.value != v.found[j]->getValue()) {
                    allSame = false;
                    if (i == options.maxDefParamSteps - 1)
                        root->addDiag(diag::DefParamCycle, getRange());
                    break;
                }
            }

            if (allSame)
                break;

            saveState(v, c);
        }

        // If we gave up due to a potential infinite loop, continue exiting.
        if (!allSame)
            break;

        SLANG_ASSERT(initialVisitor.numBlocksSeen >= numBlocksSeen);
        if (initialVisitor.numBlocksSeen == numBlocksSeen)
            break;

        generateLevel++;
        numBlocksSeen = initialVisitor.numBlocksSeen;
    }

    // We have our final overrides; copy them into the main compilation unit.
    copyStateInto(*this, true);
}

const DefinitionSymbol* Compilation::resolveConfigRules(
    std::string_view lookupName, const Scope& scope, const ConfigBlockSymbol* config,
    const ConfigRule* rule, const std::vector<DefinitionSymbol*>& defList) const {

    auto findDefByLib = [](auto& defList, const SourceLibrary* target) -> DefinitionSymbol* {
        for (auto def : defList) {
            if (def->sourceLibrary == target)
                return def;
        }
        return nullptr;
    };

    std::span<const SourceLibrary* const> liblist;
    if (!rule) {
        SLANG_ASSERT(config);
        liblist = config->defaultLiblist;
        if (auto overrideIt = config->cellOverrides.find(lookupName);
            overrideIt != config->cellOverrides.end()) {

            // There is at least one cell override with this name; look through the
            // list and take the first one that matches our library restrictions.
            for (auto& cellOverride : overrideIt->second) {
                // TODO: support this
                if (cellOverride.specificLib)
                    continue;

                rule = &cellOverride.rule;
                break;
            }
        }
    }

    if (rule) {
        auto& id = rule->useCell;
        if (!id.name.empty()) {
            auto overrideDefIt = definitionMap.find({id.name, root.get()});
            if (overrideDefIt == definitionMap.end()) {
                // TODO: error here?
                return nullptr;
            }

            const SourceLibrary* overrideLib = nullptr;
            if (id.lib.empty()) {
                if (auto parentDef = scope.asSymbol().getDeclaringDefinition())
                    overrideLib = parentDef->sourceLibrary;
            }
            else {
                overrideLib = getSourceLibrary(id.lib);
            }

            // TODO: error if not found?
            return findDefByLib(overrideDefIt->second.first, overrideLib);
        }

        // No name, so this is just a custom liblist -- search through it below.
        liblist = rule->liblist;
    }

    // This search is O(n^2) but both lists should be small
    // (or even just one element each) in basically all cases.
    for (auto lib : liblist) {
        if (auto def = findDefByLib(defList, lib))
            return def;
    }

    // Fall back to picking based on the parent instance's library.
    if (auto parentDef = scope.asSymbol().getDeclaringDefinition()) {
        if (auto def = findDefByLib(defList, parentDef->sourceLibrary))
            return def;
    }

    return nullptr;
}

} // namespace slang::ast
