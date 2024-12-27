//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"

#include "ElabVisitors.h"
#include "builtins/Builtins.h"
#include <fmt/core.h>
#include <mutex>

#include "slang/ast/ScriptSession.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/CharInfo.h"
#include "slang/text/SourceManager.h"
#include "slang/util/TimeTrace.h"

using namespace slang::parsing;

namespace slang::ast::builtins {

Builtins Builtins::Instance;

void registerGateTypes(Compilation&);
const PackageSymbol& createStdPackage(Compilation&);

} // namespace slang::ast::builtins

namespace slang::ast {

Compilation::Compilation(const Bag& options, const SourceLibrary* defaultLib) :
    options(options.getOrDefault<CompilationOptions>()), driverMapAllocator(*this),
    unrollIntervalMapAllocator(*this), tempDiag({}, {}), netAliasAllocator(*this),
    defaultLibPtr(defaultLib) {

    // Construct all built-in types.
    auto& bi = slang::ast::builtins::Builtins::Instance;
    bitType = &bi.bitType;
    logicType = &bi.logicType;
    intType = &bi.intType;
    byteType = &bi.byteType;
    integerType = &bi.integerType;
    realType = &bi.realType;
    shortRealType = &bi.shortRealType;
    stringType = &bi.stringType;
    voidType = &bi.voidType;
    errorType = &bi.errorType;

    auto regType = &bi.regType;
    auto signedBitType = &bi.signedBitType;
    auto signedLogicType = &bi.signedLogicType;
    auto signedRegType = &bi.signedRegType;
    auto shortIntType = &bi.shortIntType;
    auto longIntType = &bi.longIntType;
    auto timeType = &bi.timeType;
    auto realTimeType = &bi.realTimeType;
    auto chandleType = &bi.chandleType;
    auto nullType = &bi.nullType;
    auto eventType = &bi.eventType;
    auto unboundedType = &bi.unboundedType;
    auto typeRefType = &bi.typeRefType;
    auto untypedType = &bi.untypedType;
    auto sequenceType = &bi.sequenceType;
    auto propertyType = &bi.propertyType;

    // Register built-in types for lookup by syntax kind.
    knownTypes.reserve(32);
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

    knownNetTypes.reserve(16);
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

    // Copy in all built-in system tasks, functions, and methods.
    subroutineMap = bi.subroutineMap;
    methodMap = bi.methodMap;

    // Register the built-in std package.
    stdPkg = &builtins::createStdPackage(*this);
    packageMap.emplace(stdPkg->name, stdPkg);

    // Register the built-in gate types.
    builtins::registerGateTypes(*this);

    // Register the default library.
    if (defaultLibPtr) {
        SLANG_ASSERT(defaultLibPtr->isDefault);
    }
    else {
        defaultLibMem = std::make_unique<SourceLibrary>("work"s, INT_MAX);
        defaultLibMem->isDefault = true;
        defaultLibPtr = defaultLibMem.get();
    }
    libraryNameMap[defaultLibPtr->name] = defaultLibPtr;

    // Set a default handler for printing types and symbol paths, for convenience.
    static std::once_flag onceFlag;
    std::call_once(onceFlag, [] {
        DiagnosticEngine::setDefaultFormatter<const Type*>(std::make_unique<TypeArgFormatter>());
        DiagnosticEngine::setDefaultSymbolPathCB([](const Symbol& sym) {
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

    auto lib = tree->getSourceLibrary();
    if (lib) {
        auto& entry = libraryNameMap[lib->name];
        SLANG_ASSERT(entry == nullptr || entry == lib);
        entry = lib;
    }
    else {
        lib = defaultLibPtr;
    }

    const SyntaxNode& node = tree->root();
    const SyntaxNode* topNode = &node;
    while (topNode->parent)
        topNode = topNode->parent;

    auto unit = emplace<CompilationUnitSymbol>(*this, *lib);
    unit->setSyntax(*topNode);
    root->addMember(*unit);
    compilationUnits.push_back(unit);

    for (auto& [n, meta] : tree->getMetadata().nodeMap) {
        SyntaxMetadata result;
        result.tree = tree.get();
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

std::vector<const Symbol*> Compilation::getDefinitions() const {
    std::vector<const Symbol*> result;
    for (auto& [key, val] : definitionMap) {
        for (auto sym : val.first) {
            result.insert(std::ranges::upper_bound(result, sym->name, {},
                                                   [](auto item) { return item->name; }),
                          sym);
        }
    }

    return result;
}

std::vector<const PackageSymbol*> Compilation::getPackages() const {
    std::vector<const PackageSymbol*> result;
    for (auto& [name, pkg] : packageMap) {
        result.insert(
            std::ranges::upper_bound(result, name, {}, [](auto item) { return item->name; }), pkg);
    }
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
    SmallVector<std::pair<DefinitionLookupResult, SourceRange>> topDefs;
    if (options.topModules.empty()) {
        for (auto& [key, defList] : definitionMap) {
            if (std::get<1>(key) != root.get())
                continue;

            for (auto defSym : defList.first) {
                // Ignore definitions that are not top level. Top level definitions are:
                // - Modules and programs
                // - Not nested
                // - Have no non-defaulted parameters
                // - Not instantiated anywhere
                // - Not in a library
                if (defSym->kind != SymbolKind::Definition)
                    continue;

                auto& def = defSym->as<DefinitionSymbol>();
                if (!def.sourceLibrary.isDefault ||
                    globalInstantiations.find(def.name) != globalInstantiations.end()) {
                    continue;
                }

                // Library definitions are never automatically instantiated in any capacity.
                if (!def.syntaxTree || !def.syntaxTree->isLibraryUnit) {
                    if (def.definitionKind == DefinitionKind::Module ||
                        def.definitionKind == DefinitionKind::Program) {
                        if (isValidTop(def)) {
                            // This definition can be automatically instantiated.
                            topDefs.push_back({{&def}, {}});
                            continue;
                        }
                    }
                }

                // Otherwise this definition is unreferenced and not automatically instantiated.
                unreferencedDefs.push_back(&def);
            }
        }
    }
    else {
        SmallMap<std::string_view, size_t, 4> topNameMap;
        auto tryAddTop = [&](DefinitionLookupResult result, SourceRange sourceRange) {
            // Make sure this definition's name doesn't collide with a top
            // module we already previously selected.
            auto def = result.definition;
            auto [it, inserted] = topNameMap.emplace(def->name, topDefs.size());
            if (inserted) {
                topDefs.push_back({result, sourceRange});
                SLANG_ASSERT(def->kind == SymbolKind::Definition);
                def->as<DefinitionSymbol>().noteInstantiated();
            }
            else {
                auto& diag = root->addDiag(diag::MultipleTopDupName, sourceRange.start()
                                                                         ? sourceRange
                                                                         : SourceRange::NoLocation);
                diag << def->name;

                auto& entry = topDefs[it->second];
                if (entry.first.configRoot)
                    diag.addNote(diag::NoteConfigRule, entry.second);
            }
        };

        // If the list of top modules has already been provided we just need to
        // find and instantiate them.
        for (auto userProvidedName : options.topModules) {
            // Find the target library, if there is one specified.
            auto searchName = userProvidedName;
            const SourceLibrary* targetLib = nullptr;
            if (auto idx = searchName.find('.'); idx != std::string_view::npos) {
                targetLib = getSourceLibrary(searchName.substr(0, idx));
                if (!targetLib) {
                    root->addDiag(diag::InvalidTopModule, SourceLocation::NoLocation)
                        << userProvidedName;
                    continue;
                }

                searchName = searchName.substr(idx + 1);
            }

            // A trailing ':config' is stripped -- it's there to allow the user
            // to disambiguate modules and config blocks.
            bool onlyConfig = false;
            constexpr std::string_view configSuffix = ":config";
            if (searchName.ends_with(configSuffix)) {
                onlyConfig = true;
                searchName = searchName.substr(0, searchName.length() - configSuffix.length());
            }

            if (!onlyConfig) {
                if (auto defIt = definitionMap.find(std::tuple{searchName, root.get()});
                    defIt != definitionMap.end()) {

                    const DefinitionSymbol* foundDef = nullptr;
                    for (auto defSym : defIt->second.first) {
                        if (defSym->kind != SymbolKind::Definition)
                            continue;

                        auto& def = defSym->as<DefinitionSymbol>();
                        if (&def.sourceLibrary == targetLib ||
                            (!targetLib && def.sourceLibrary.isDefault)) {
                            foundDef = &def;
                            break;
                        }
                    }

                    if (foundDef) {
                        if ((foundDef->definitionKind == DefinitionKind::Module ||
                             foundDef->definitionKind == DefinitionKind::Program) &&
                            isValidTop(*foundDef)) {

                            tryAddTop({foundDef}, {});
                        }
                        else {
                            // Otherwise, issue an error because the user asked us to instantiate
                            // this.
                            foundDef->getParentScope()->addDiag(diag::InvalidTopModule,
                                                                SourceLocation::NoLocation)
                                << userProvidedName;
                        }
                        continue;
                    }
                }
            }

            if (auto confIt = configBlocks.find(searchName); confIt != configBlocks.end()) {
                const ConfigBlockSymbol* foundConf = nullptr;
                for (auto conf : confIt->second) {
                    auto lib = conf->getSourceLibrary();
                    SLANG_ASSERT(lib);

                    if (lib == targetLib || (!targetLib && lib->isDefault)) {
                        foundConf = conf;
                        break;
                    }
                }

                if (foundConf) {
                    foundConf->isUsed = true;
                    for (auto& cell : foundConf->getTopCells())
                        tryAddTop({&cell.definition, foundConf, cell.rule}, cell.sourceRange);
                    continue;
                }
            }

            root->addDiag(diag::InvalidTopModule, SourceLocation::NoLocation) << userProvidedName;
        }

        // Go back through the definition map and find all definitions that are unused,
        // unreferenced in the design, and candidates for instantiating in unreferenced
        // form to get some error checking of their contents.
        for (auto& [key, defList] : definitionMap) {
            if (std::get<1>(key) != root.get())
                continue;

            for (auto defSym : defList.first) {
                if (defSym->kind != SymbolKind::Definition)
                    continue;

                auto& def = defSym->as<DefinitionSymbol>();
                if (globalInstantiations.find(def.name) == globalInstantiations.end() &&
                    def.sourceLibrary.isDefault && def.getInstanceCount() == 0) {
                    unreferencedDefs.push_back(&def);
                }
            }
        }
    }

    // Sort the list of definitions so that we get deterministic ordering of instances;
    // the order is otherwise dependent on iterating over a hash table.
    std::ranges::sort(topDefs, [](auto a, auto b) {
        return a.first.definition->name < b.first.definition->name;
    });
    std::ranges::sort(unreferencedDefs, [](auto a, auto b) { return a->name < b->name; });

    // If we have any cli param overrides we should apply them to
    // each top-level instance.
    // TODO: generalize these to full hierarchical paths
    if (!cliOverrides.empty()) {
        for (auto [result, _] : topDefs) {
            auto& def = result.definition->as<DefinitionSymbol>();
            for (auto& param : def.parameters) {
                if (!param.isTypeParam && param.hasSyntax) {
                    auto it = cliOverrides.find(param.name);
                    if (it != cliOverrides.end()) {
                        hierarchyOverrides.childNodes[*def.getSyntax()].paramOverrides.emplace(
                            param.valueDecl, std::pair{*it->second, nullptr});
                    }
                }
            }
        }
    }

    SmallVector<const InstanceSymbol*> topList;
    for (auto [result, _] : topDefs) {
        auto& def = result.definition->as<DefinitionSymbol>();
        HierarchyOverrideNode* hierarchyOverrideNode = nullptr;
        if (auto sit = hierarchyOverrides.childNodes.find(*def.getSyntax());
            sit != hierarchyOverrides.childNodes.end()) {
            hierarchyOverrideNode = &sit->second;
        }

        auto& instance = InstanceSymbol::createDefault(*this, def, hierarchyOverrideNode,
                                                       result.configRoot, result.configRule);
        root->addMember(instance);
        topList.push_back(&instance);
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

Compilation::DefinitionLookupResult Compilation::tryGetDefinition(std::string_view lookupName,
                                                                  const Scope& scope) const {
    // Try to find a config block for this scope to help choose the right definition.
    const ResolvedConfig* resolvedConfig = nullptr;
    if (auto inst = scope.getContainingInstance(); inst && inst->parentInstance)
        resolvedConfig = inst->parentInstance->resolvedConfig;

    // Always search in the root scope to start. Most definitions are global.
    auto it = definitionMap.find({lookupName, root.get()});
    if (it == definitionMap.end()) {
        // If there's a config it might be able to provide an
        // override for this cell name.
        if (resolvedConfig)
            return resolveConfigRules(lookupName, scope, resolvedConfig, nullptr, {}).first;
        return {};
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
    if (resolvedConfig)
        return resolveConfigRules(lookupName, scope, resolvedConfig, nullptr, defList).first;

    // If there is a global priority list try to use that.
    for (auto lib : defaultLiblist) {
        for (auto def : defList) {
            if (def->getSourceLibrary() == lib)
                return def;
        }
    }

    // Otherwise return the first definition in the list -- it's already
    // sorted in priority order.
    return defList.empty() ? DefinitionLookupResult{} : DefinitionLookupResult{defList.front()};
}

static Token getExternNameToken(const SyntaxNode& sn) {
    return sn.kind == SyntaxKind::ExternModuleDecl ? sn.as<ExternModuleDeclSyntax>().header->name
                                                   : sn.as<ExternUdpDeclSyntax>().name;
}

Compilation::DefinitionLookupResult Compilation::getDefinition(std::string_view name,
                                                               const Scope& scope,
                                                               SourceRange sourceRange,
                                                               DiagCode code) const {
    if (auto result = tryGetDefinition(name, scope); result.definition)
        return result;

    errorMissingDef(name, scope, sourceRange, code);
    return {};
}

Compilation::DefinitionLookupResult Compilation::getDefinition(std::string_view lookupName,
                                                               const Scope& scope,
                                                               const ConfigRule& configRule,
                                                               SourceRange sourceRange,
                                                               DiagCode code) const {
    std::pair<DefinitionLookupResult, bool> result;
    if (auto it = definitionMap.find({lookupName, root.get()}); it != definitionMap.end())
        result = resolveConfigRules(lookupName, scope, nullptr, &configRule, it->second.first);
    else
        result = resolveConfigRules(lookupName, scope, nullptr, &configRule, {});

    if (!result.first.definition && !result.second) {
        // No definition found and no error issued, so issue one ourselves.
        auto diag = errorMissingDef(lookupName, scope, sourceRange, code);
        if (diag)
            diag->addNote(diag::NoteConfigRule, configRule.syntax->sourceRange());
    }

    return result.first;
}

Compilation::DefinitionLookupResult Compilation::getDefinition(
    std::string_view name, const Scope& scope, SourceRange sourceRange,
    const BindDirectiveInfo& bindInfo) const {

    DefinitionLookupResult result;
    if (bindInfo.instantiationDefSyntax) {
        switch (bindInfo.instantiationDefSyntax->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                auto& mds = bindInfo.instantiationDefSyntax->as<ModuleDeclarationSyntax>();
                result.definition = getDefinition(scope, mds);
                if (!result.definition)
                    errorMissingDef(name, scope, sourceRange, diag::UnknownModule);
                break;
            }
            case SyntaxKind::UdpDeclaration:
                scope.addDiag(diag::BindTargetPrimitive, sourceRange);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }
    else {
        errorMissingDef(name, scope, sourceRange, diag::UnknownModule);
    }

    if (auto it = configBySyntax.find(bindInfo.configBlockSyntax); it != configBySyntax.end())
        result.configRoot = it->second;

    if (auto it = configBySyntax.find(bindInfo.configRuleSyntax); it != configBySyntax.end()) {
        // This rule maps to a config block, so map further to the actual rule object.
        result.configRule = it->second->findRuleFromSyntax(*bindInfo.configRuleSyntax);
    }

    return result;
}

const DefinitionSymbol* Compilation::getDefinition(const Scope& scope,
                                                   const ModuleDeclarationSyntax& syntax) const {
    if (auto it = definitionFromSyntax.find(&syntax); it != definitionFromSyntax.end()) {
        SmallMap<const Scope*, const DefinitionSymbol*, 4> scopeMap;
        for (auto def : it->second) {
            auto insertScope = def->getParentScope();
            if (insertScope && insertScope->asSymbol().kind == SymbolKind::CompilationUnit)
                insertScope = root.get();

            scopeMap[insertScope] = def;
        }

        auto lookupScope = &scope;
        do {
            if (auto scopeIt = scopeMap.find(lookupScope); scopeIt != scopeMap.end())
                return scopeIt->second;

            lookupScope = lookupScope->asSymbol().getParentScope();
        } while (lookupScope);
    }
    return nullptr;
}

const DefinitionSymbol* Compilation::getDefinition(const ConfigBlockSymbol& config,
                                                   std::string_view cellName,
                                                   std::string_view libName,
                                                   SourceRange sourceRange) const {
    if (auto defIt = definitionMap.find(std::tuple{cellName, root.get()});
        defIt != definitionMap.end()) {

        const DefinitionSymbol* foundDef = nullptr;
        for (auto defSym : defIt->second.first) {
            if (defSym->kind != SymbolKind::Definition)
                continue;

            auto& def = defSym->as<DefinitionSymbol>();
            if (def.sourceLibrary.name == libName ||
                (libName.empty() && &def.sourceLibrary == config.getSourceLibrary())) {
                foundDef = &def;
                break;
            }
        }

        if (foundDef && (foundDef->definitionKind == DefinitionKind::Module ||
                         foundDef->definitionKind == DefinitionKind::Program)) {
            return foundDef;
        }
    }

    std::string errorName;
    if (!libName.empty())
        errorName = fmt::format("{}.{}", libName, cellName);
    else
        errorName = cellName;

    root->addDiag(diag::InvalidTopModule, sourceRange) << errorName;
    return nullptr;
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
                       metadata.timeScale, metadata.tree))
                   .get();
    definitionFromSyntax[&syntax].push_back(def);

    insertDefinition(*def, scope);

    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    const bool isRoot = targetScope == root.get();
    if (isRoot)
        checkElemTimeScale(def->timeScale, syntax.header->name.range());
}

void Compilation::insertDefinition(Symbol& symbol, const Scope& scope) {
    auto reportRedefinition = [&](SourceLocation oldLoc, DiagCode code) {
        if (!symbol.name.empty()) {
            auto& diag = scope.addDiag(code, symbol.location);
            diag << symbol.name;
            diag.addNote(diag::NotePreviousDefinition, oldLoc);
        }
    };

    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    const bool isRoot = targetScope == root.get();
    auto key = std::tuple(symbol.name, targetScope);
    if (symbol.name.empty())
        return;

    if (auto it = definitionMap.find(key); it != definitionMap.end()) {
        // There is already a definition with this name in this scope.
        // If we're not at the root scope, it's a straightforward error.
        auto& defList = it->second.first;
        if (!isRoot) {
            SLANG_ASSERT(defList[0]);
            reportRedefinition(defList[0]->location, diag::DuplicateDefinition);
            return;
        }

        // Otherwise we have a duplicate at the root scope; figure out where
        // we should insert this definition. If they are in different libraries
        // then keep them sorted in priority order. If they're in the same library
        // then we want to error (or maybe warn).
        auto vecIt = std::ranges::lower_bound(defList, &symbol, [](auto a, auto b) {
            auto libA = a->getSourceLibrary();
            auto libB = b->getSourceLibrary();
            SLANG_ASSERT(libA && libB);
            return libA->priority < libB->priority;
        });

        if (vecIt != defList.end()) {
            bool warned = false;
            auto symLib = symbol.getSourceLibrary();
            for (auto v = vecIt; v != defList.end(); v++) {
                auto vSym = *v;
                auto vLib = vSym->getSourceLibrary();
                if (vLib == symLib) {
                    // Duplicate in the same library. If they are both the same kind
                    // then we report a warning and take the first one, otherwise
                    // we give a hard error.
                    if (vSym->kind == symbol.kind) {
                        if (!warned) {
                            // We keep going after this because there might also
                            // be a mismatching primitive / definition worth erroring about
                            // and the DuplicateDefinition warning can be suppressed.
                            reportRedefinition(vSym->location, diag::DuplicateDefinition);
                            warned = true;
                        }
                    }
                    else {
                        reportRedefinition(vSym->location, diag::Redefinition);
                        return;
                    }
                }
                else if (vLib->priority != symLib->priority) {
                    // We know for sure there are no more duplicates because the
                    // library and/or the priority has changed.
                    break;
                }
            }
        }

        defList.insert(vecIt, &symbol);
    }
    else {
        definitionMap.emplace(key, std::pair{std::vector{&symbol}, !isRoot});
    }

    if (isRoot) {
        // TODO: how do extern modules work with libraries?
        if (auto externDef = getExternDefinition(symbol.name, scope)) {
            auto syntax = symbol.getSyntax();
            SLANG_ASSERT(syntax);

            if (externDef->kind == SyntaxKind::ExternModuleDecl &&
                symbol.kind == SymbolKind::Definition) {
                checkExternModMatch(scope, *externDef->as<ExternModuleDeclSyntax>().header,
                                    *syntax->as<ModuleDeclarationSyntax>().header,
                                    diag::ExternDeclMismatchImpl);
            }
            else if (externDef->kind == SyntaxKind::ExternUdpDecl &&
                     symbol.kind == SymbolKind::Primitive) {
                checkExternUdpMatch(scope, *externDef->as<ExternUdpDeclSyntax>().portList,
                                    *syntax->as<UdpDeclarationSyntax>().portList, symbol.name,
                                    diag::ExternDeclMismatchImpl);
            }
            else {
                reportRedefinition(getExternNameToken(*externDef).location(), diag::Redefinition);
            }
        }
    }
    else {
        // Record the fact that we have nested modules with this name.
        definitionMap[std::tuple(symbol.name, root.get())].second = true;
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
    auto& config = ConfigBlockSymbol::fromSyntax(scope, syntax);

    // Register lookups by syntax node. Note that we register rule entries here
    // by looking directly at the syntax so that we don't trigger resolution
    // of the config block early, which could cause spurious errors.
    configBySyntax[config.getSyntax()] = &config;
    for (auto ruleSyntax : syntax.rules)
        configBySyntax[ruleSyntax] = &config;

    if (!config.name.empty()) {
        auto it = configBlocks.find(config.name);
        if (it == configBlocks.end()) {
            configBlocks.emplace(config.name, std::vector<const ConfigBlockSymbol*>{&config});
        }
        else {
            auto configLib = scope.asSymbol().getSourceLibrary();
            auto findIt = std::ranges::find_if(it->second, [&](const ConfigBlockSymbol* elem) {
                return elem->getSourceLibrary() == configLib;
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
    }

    return config;
}

const PrimitiveSymbol& Compilation::createPrimitive(Scope& scope,
                                                    const UdpDeclarationSyntax& syntax) {
    auto& prim = PrimitiveSymbol::fromSyntax(scope, syntax);
    scope.addMember(prim);
    insertDefinition(prim, scope);
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

void Compilation::addSystemSubroutine(const std::shared_ptr<SystemSubroutine>& subroutine) {
    subroutineMap.emplace(subroutine->name, subroutine);
}

void Compilation::addSystemMethod(SymbolKind typeKind,
                                  const std::shared_ptr<SystemSubroutine>& method) {
    methodMap.emplace(std::make_tuple(std::string_view(method->name), typeKind), method);
}

const SystemSubroutine* Compilation::getSystemSubroutine(std::string_view name) const {
    auto it = subroutineMap.find(name);
    if (it == subroutineMap.end())
        return nullptr;
    return it->second.get();
}

const SystemSubroutine* Compilation::getSystemMethod(SymbolKind typeKind,
                                                     std::string_view name) const {
    auto it = methodMap.find(std::make_tuple(name, typeKind));
    if (it == methodMap.end())
        return nullptr;
    return it->second.get();
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

void Compilation::noteBindDirective(const BindDirectiveSyntax& syntax, const Scope& scope) {
    if (!scope.isUninstantiated())
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

void Compilation::noteNetAlias(const Scope& scope, const Symbol& firstSym,
                               DriverBitRange firstRange, const Expression& firstExpr,
                               const Symbol& secondSym, DriverBitRange secondRange,
                               const Expression& secondExpr) {
    SLANG_ASSERT(firstRange.second - firstRange.first == secondRange.second - secondRange.first);

    auto overlaps = [](DriverBitRange a, DriverBitRange b) {
        return a.first <= b.second && b.first <= a.second;
    };

    const Symbol* a = &firstSym;
    const Symbol* b = &secondSym;
    const Expression* firstExprPtr = &firstExpr;
    const Expression* secondExprPtr = &secondExpr;
    if (a > b) {
        std::swap(a, b);
        std::swap(firstRange, secondRange);
        std::swap(firstExprPtr, secondExprPtr);
    }

    bool errored = false;
    auto& imap = netAliases[a];
    const auto end = imap.end();
    for (auto it = imap.find(firstRange); it != end; ++it) {
        auto curr = *it;
        if (curr->sym == b && overlaps(curr->range, secondRange)) {
            errored = true;
            if (curr->sym == a) {
                scope.addDiag(diag::NetAliasSelf, firstExprPtr->sourceRange)
                    << secondExprPtr->sourceRange;
            }
            else {
                auto& diag = scope.addDiag(diag::MultipleNetAlias, firstExprPtr->sourceRange);
                diag.addNote(diag::NoteAliasedTo, secondExprPtr->sourceRange);
                diag.addNote(diag::NoteAliasDeclaration, curr->firstExpr->sourceRange);
                diag.addNote(diag::NoteAliasedTo, curr->secondExpr->sourceRange);
            }
            break;
        }
    }

    auto newAlias = emplace<NetAlias>(b, secondRange, firstExprPtr, secondExprPtr);
    imap.insert(firstRange, newAlias, netAliasAllocator);

    if (!errored && a == b && overlaps(firstRange, secondRange)) {
        scope.addDiag(diag::NetAliasSelf, firstExprPtr->sourceRange) << secondExprPtr->sourceRange;
    }
}

void Compilation::noteHierarchicalReference(const Scope& initialScope,
                                            const HierarchicalReference& ref) {
    // For now, we're only interested in upward names that cross
    // through instance boundaries.
    SLANG_ASSERT(ref.expr);
    auto currScope = &initialScope;
    for (size_t i = 0; i < ref.upwardCount; i++) {
        auto& sym = currScope->asSymbol();
        if (sym.kind == SymbolKind::InstanceBody)
            hierRefMap[&sym].push_back(&ref);

        currScope = sym.getHierarchicalParent();
        SLANG_ASSERT(currScope);
    }
}

void Compilation::noteVirtualIfaceInstance(const InstanceSymbol& symbol) {
    virtualInterfaceInstances.push_back(&symbol);
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

void Compilation::noteExternDefinition(const Scope& scope, const SyntaxNode& syntax) {
    auto nameToken = getExternNameToken(syntax);
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    auto [it, inserted] = externDefMap.emplace(std::tuple(name, targetScope), &syntax);
    if (!inserted) {
        if (syntax.kind != it->second->kind) {
            auto& diag = scope.addDiag(diag::Redefinition, nameToken.location());
            diag << name;
            diag.addNote(diag::NotePreviousDefinition, getExternNameToken(*it->second).location());
        }
        else if (syntax.kind == SyntaxKind::ExternModuleDecl) {
            checkExternModMatch(scope, *syntax.as<ExternModuleDeclSyntax>().header,
                                *it->second->as<ExternModuleDeclSyntax>().header,
                                diag::ExternDeclMismatchPrev);
        }
        else {
            checkExternUdpMatch(scope, *syntax.as<ExternUdpDeclSyntax>().portList,
                                *it->second->as<ExternUdpDeclSyntax>().portList, name,
                                diag::ExternDeclMismatchPrev);
        }
    }
}

const SyntaxNode* Compilation::getExternDefinition(std::string_view name,
                                                   const Scope& scope) const {
    if (!externDefMap.empty()) {
        const Scope* searchScope = &scope;
        do {
            auto it = externDefMap.find(std::make_tuple(name, searchScope));
            if (it != externDefMap.end())
                return it->second;

            searchScope = searchScope->asSymbol().getParentScope();
        } while (searchScope);
    }

    return nullptr;
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
    auto unit = emplace<CompilationUnitSymbol>(*this, getDefaultLibrary());
    root->addMember(*unit);
    return *unit;
}

void Compilation::elaborate() {
    // Touch every symbol, scope, statement, and expression tree so that
    // we can be sure we have all the diagnostics.
    uint32_t errorLimit = options.errorLimit == 0 ? UINT32_MAX : options.errorLimit;
    DiagnosticVisitor elabVisitor(*this, numErrors, errorLimit);
    getRoot().visit(elabVisitor);

    if (elabVisitor.finishedEarly())
        return;

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
    // resolved prior to full elaboration but their diagnostics were not
    // issued so we need to check again.
    for (auto [directive, scope] : bindDirectives) {
        ResolvedBind resolvedBind;
        resolveBindTargets(*directive, *scope, resolvedBind);
        checkBindTargetParams(*directive, *scope, resolvedBind);
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

    // Report on unused config rules.
    if (!configBlocks.empty()) {
        for (auto& [name, confList] : configBlocks) {
            for (auto config : confList) {
                if (config->isUsed)
                    config->checkUnusedRules();
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
        TimeTraceScope timeScope("postElabVisitors"sv, ""sv);

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

            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib()) {
                def->getParentScope()->addDiag(diag::UnusedDefinition, def->location)
                    << def->getKindString();
            }
        }

        PostElabVisitor postElabVisitor(*this);
        getRoot().visit(postElabVisitor);
    }
}

const Diagnostics& Compilation::getParseDiagnostics() {
    if (cachedParseDiagnostics)
        return *cachedParseDiagnostics;

    cachedParseDiagnostics.emplace();
    for (auto& tree : syntaxTrees)
        cachedParseDiagnostics->append_range(tree->diagnostics());

    if (sourceManager)
        cachedParseDiagnostics->sort(*sourceManager);
    return *cachedParseDiagnostics;
}

const Diagnostics& Compilation::getSemanticDiagnostics() {
    if (cachedSemanticDiagnostics)
        return *cachedSemanticDiagnostics;

    // Elaborate the design.
    elaborate();

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
                    if (!checkerBody.flags.has(InstanceFlags::Uninstantiated)) {
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
            inst->as<InstanceSymbol>().getDefinition().getInstanceCount() > count) {
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
    if (diagsDisabled) {
        tempDiag = std::move(diag);
        return tempDiag;
    }

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

Scope::WildcardImportData* Compilation::allocWildcardImportData() {
    return wildcardImportAllocator.emplace();
}

const ImplicitTypeSyntax& Compilation::createEmptyTypeSyntax(SourceLocation loc) {
    return *emplace<ImplicitTypeSyntax>(Token(), nullptr,
                                        Token(*this, TokenKind::Placeholder, {}, {}, loc));
}

void Compilation::forceElaborate(const Symbol& symbol) {
    DiagnosticVisitor visitor(*this, numErrors,
                              options.errorLimit == 0 ? UINT32_MAX : options.errorLimit);
    visitor.visitInstances = false;
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
                                     ResolvedBind& resolvedBind) {
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
        auto targetDef =
            getDefinition(name.valueText(), scope, name.range(), diag::UnknownModule).definition;
        if (!targetDef)
            return;

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
                    resolvedBind.instTargets.push_back(result.found);
                }
            }
        }
    }
    else {
        LookupResult result;
        Lookup::name(*syntax.target, context, flags, result);

        if (result.found) {
            if (checkValidTarget(*result.found, *syntax.target))
                resolvedBind.instTargets.push_back(result.found);
        }
        else {
            // If we didn't find the name as an instance, try as a definition.
            if (syntax.target->kind == SyntaxKind::IdentifierName) {
                Token name = syntax.target->as<IdentifierNameSyntax>().identifier;
                auto def = getDefinition(name.valueText(), scope, name.range(), diag::UnknownModule)
                               .definition;
                if (!def)
                    return;

                if (def->kind == SymbolKind::Definition)
                    resolvedBind.defTarget = &def->as<DefinitionSymbol>();
            }
        }

        if (!resolvedBind.defTarget)
            result.reportDiags(context);
    }

    // Resolve the actual instantiation definition now, since it depends on the current
    // config mapping, not the mapping of the target scope(s).
    if (syntax.instantiation->kind == SyntaxKind::HierarchyInstantiation) {
        auto& his = syntax.instantiation->as<HierarchyInstantiationSyntax>();
        resolvedBind.instanceDef = tryGetDefinition(his.type.valueText(), scope);

        // If we did not directly resolve to a new config root, look for a config
        // in our parent scope. If there is one, pretend we've created a new
        // config root at the targeted bind instance, so that modules underneath
        // the bound instance get the correct config.
        if (!resolvedBind.instanceDef.configRoot) {
            if (auto inst = scope.getContainingInstance(); inst && inst->parentInstance)
                resolvedBind.resolvedConfig = inst->parentInstance->resolvedConfig;
        }
    }
}

void Compilation::checkBindTargetParams(const syntax::BindDirectiveSyntax& syntax,
                                        const Scope& scope, const ResolvedBind& resolvedBind) {
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
            for (auto param : inst.body.getParameters()) {
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

    for (auto target : resolvedBind.instTargets)
        doCheck(target->as<InstanceSymbol>().body);

    if (resolvedBind.defTarget) {
        auto it = instancesWithDefBinds.find(resolvedBind.defTarget);
        if (it != instancesWithDefBinds.end()) {
            for (auto target : it->second)
                doCheck(target->as<InstanceBodySymbol>());
        }
    }
}

void Compilation::checkVirtualIfaceInstance(const InstanceSymbol& instance) {
    auto body = instance.getCanonicalBody();
    if (!body)
        body = &instance.body;

    if (auto it = hierRefMap.find(body); it != hierRefMap.end()) {
        auto& diag = body->addDiag(diag::VirtualIfaceHierRef, instance.location);
        for (auto ref : it->second)
            diag.addNote(diag::NoteHierarchicalRef, ref->expr->sourceRange);
    }

    Diagnostic* portDiag = nullptr;
    for (auto port : body->getPortList()) {
        if (port->kind == SymbolKind::InterfacePort) {
            if (!portDiag)
                portDiag = &body->addDiag(diag::VirtualIfaceIfacePort, instance.location);
            portDiag->addNote(diag::NoteDeclarationHere, port->location);
        }
    }
}

void Compilation::resolveDefParamsAndBinds() {
    TimeTraceScope timeScope("resolveDefParamsAndBinds"sv, ""sv);

    struct OverrideEntry {
        OpaqueInstancePath path;
        const SyntaxNode* targetSyntax = nullptr;
        const SyntaxNode* defparamSyntax = nullptr;
        ConstantValue value;
        std::string pathStr;
    };
    SmallVector<OverrideEntry, 4> overrides;

    struct BindEntry {
        OpaqueInstancePath path;
        const ModuleDeclarationSyntax* definitionTarget = nullptr;
        BindDirectiveInfo info;
    };
    SmallVector<BindEntry> binds;

    auto getNodeFor = [](const OpaqueInstancePath& path, Compilation& c) {
        HierarchyOverrideNode* node = &c.hierarchyOverrides;
        for (auto& entry : path.entries)
            node = &node->childNodes[entry];
        return node;
    };

    auto copyStateInto = [&](Compilation& c, bool isFinal) {
        for (auto& entry : overrides) {
            if (!entry.targetSyntax)
                continue;

            SLANG_ASSERT(entry.defparamSyntax);

            auto node = getNodeFor(entry.path, c);
            auto [it, inserted] = node->paramOverrides.emplace(
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
                if (!entry.path.empty()) {
                    // This is a nested definition, so we need to put the
                    // bind into the override node.
                    auto node = getNodeFor(entry.path, c);
                    node->binds.push_back({entry.info, entry.definitionTarget});
                }
                else {
                    auto def = c.getDefinition(*c.root, *entry.definitionTarget);
                    if (def) {
                        // const_cast is fine; we accessed the private data of the compilation
                        // through a public interface that added the const on top.
                        const_cast<DefinitionSymbol*>(def)->bindDirectives.push_back(entry.info);
                    }
                }
            }
            else {
                auto node = getNodeFor(entry.path, c);
                node->binds.push_back({entry.info, nullptr});
            }
        }
    };

    auto cloneInto = [&](Compilation& c) {
        c.diagsDisabled = true;
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

                overrides.push_back({OpaqueInstancePath(*target), target->getSyntax(),
                                     defparam->getSyntax(), defparam->getValue(), std::move(path)});
            }
        }

        // We make a copy of the bind directives list here because resolveBindTargets
        // can cause the compilation to add more entries to the list (for recursive
        // module instantiations).
        binds.clear();
        auto bindDirs = c.bindDirectives;
        for (auto [syntax, scope] : bindDirs) {
            ResolvedBind resolvedBind;
            c.resolveBindTargets(*syntax, *scope, resolvedBind);

            BindDirectiveInfo info;
            info.bindSyntax = syntax;

            auto& def = resolvedBind.instanceDef;
            info.configRuleSyntax = def.configRule ? def.configRule->syntax.get() : nullptr;
            info.configBlockSyntax = def.configRoot ? def.configRoot->getSyntax() : nullptr;
            info.instantiationDefSyntax = def.definition ? def.definition->getSyntax() : nullptr;
            info.isNewConfigRoot = def.configRoot != nullptr;
            if (!info.isNewConfigRoot && resolvedBind.resolvedConfig) {
                info.configBlockSyntax = resolvedBind.resolvedConfig->useConfig.getSyntax();

                // Make a copy of the list; the memory for it is owned by
                // the old compilation that is going away.
                info.liblist = copyFrom(resolvedBind.resolvedConfig->liblist);
            }

            for (auto target : resolvedBind.instTargets)
                binds.emplace_back(BindEntry{OpaqueInstancePath(*target), nullptr, info});

            if (auto defTarget = resolvedBind.defTarget) {
                auto parentScope = defTarget->getParentScope();
                auto defSyntax = defTarget->getSyntax();
                SLANG_ASSERT(parentScope && defSyntax);

                // If this is a nested definition we'll put it into the
                // override node of the parent scope that contains the
                // definition. Otherwise it's a globally targeted bind.
                OpaqueInstancePath path;
                auto& parentSym = parentScope->asSymbol();
                if (parentSym.kind != SymbolKind::CompilationUnit)
                    path = OpaqueInstancePath(parentSym);

                binds.emplace_back(
                    BindEntry{std::move(path), &defSyntax->as<ModuleDeclarationSyntax>(), info});
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
    size_t numDefParamsSeen = 0;
    while (true) {
        // Traverse the design and find all defparams and their values.
        // defparam resolution happens in a cloned compilation unit because we will be
        // constantly mucking with parameter values in ways that can change the actual
        // hierarchy that gets instantiated. Cloning lets us do that in an isolated context
        // and throw that work away once we know the final parameter values.
        Compilation initialClone({}, defaultLibPtr);
        cloneInto(initialClone);

        size_t currBlocksSeen;
        auto nextIt = [&] {
            // If we haven't found any new blocks we're done iterating.
            SLANG_ASSERT(currBlocksSeen >= numBlocksSeen);
            if (currBlocksSeen == numBlocksSeen)
                return true;

            // Otherwise advance into the next blocks and try again.
            generateLevel++;
            numBlocksSeen = currBlocksSeen;
            return false;
        };

        while (true) {
            DefParamVisitor v(options.maxInstanceDepth, generateLevel);
            initialClone.getRoot(/* skipDefParamsAndBinds */ true).visit(v);
            if (checkProblem(v))
                return;

            currBlocksSeen = v.numBlocksSeen;
            if (v.found.size() > numDefParamsSeen ||
                initialClone.bindDirectives.size() > numBindsSeen) {
                numDefParamsSeen = v.found.size();
                saveState(v, initialClone);
                break;
            }

            // We didn't find any more binds or defparams so increase
            // our generate level and try again.
            if (nextIt()) {
                saveState(v, initialClone);
                break;
            }
        }

        // If we have found more binds, do another visit to let them be applied
        // and potentially add blocks and defparams to our set for this level.
        if (initialClone.bindDirectives.size() > numBindsSeen) {
            // Reset the number of defparams seen to ensure that
            // we re-resolve everything after the next iteration.
            numDefParamsSeen = 0;
            numBindsSeen = initialClone.bindDirectives.size();
            continue;
        }

        // defparams can change the value of parameters, further affecting the value of
        // other defparams elsewhere in the design. This means we need to iterate,
        // reevaluating defparams until they all settle to a stable value or until we
        // give up due to the potential of cyclical references.
        bool allSame = true;
        for (uint32_t i = 0; i < options.maxDefParamSteps; i++) {
            Compilation c({}, defaultLibPtr);
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

        if (nextIt())
            break;
    }

    // We have our final overrides; copy them into the main compilation unit.
    copyStateInto(*this, true);
}

template<typename TDefList>
auto findDefByLib(TDefList& defList, const SourceLibrary& target)
    -> std::remove_reference_t<decltype(defList[0])> {
    for (auto def : defList) {
        if (def->getSourceLibrary() == &target)
            return def;
    }
    return nullptr;
}

std::pair<Compilation::DefinitionLookupResult, bool> Compilation::resolveConfigRule(
    const Scope& scope, const ConfigRule& rule) const {

    rule.isUsed = true;
    auto& id = rule.useCell;
    SLANG_ASSERT(!id.name.empty());

    // Figure out the target library.
    const SourceLibrary* overrideLib = defaultLibPtr;
    if (id.lib.empty()) {
        if (auto parentDef = scope.asSymbol().getDeclaringDefinition())
            overrideLib = &parentDef->sourceLibrary;
    }
    else {
        overrideLib = getSourceLibrary(id.lib);
        if (!overrideLib) {
            root->addDiag(diag::UnknownLibrary, id.sourceRange) << id.lib;
            return {{}, true};
        }
    }

    if (!id.targetConfig) {
        if (auto overrideDefIt = definitionMap.find({id.name, root.get()});
            overrideDefIt != definitionMap.end()) {
            // There are definitions with this name; find the one that
            // matches our target library.
            auto result = findDefByLib(overrideDefIt->second.first, *overrideLib);
            if (result)
                return {{result, nullptr, &rule}, true};
        }
    }

    // If we didn't find a target definition, try to look for a config.
    if (auto configIt = configBlocks.find(id.name); configIt != configBlocks.end()) {
        auto result = findDefByLib(configIt->second, *overrideLib);
        if (result) {
            result->isUsed = true;
            auto topCells = result->getTopCells();
            if (topCells.size() != 1) {
                auto syntax = result->getSyntax();
                SLANG_ASSERT(syntax);

                auto range = syntax->as<ConfigDeclarationSyntax>().topCells.sourceRange();
                auto& diag = scope.addDiag(diag::NestedConfigMultipleTops, range);
                diag << result->name;
                diag.addNote(diag::NoteConfigRule, rule.syntax->sourceRange());

                return {{}, true};
            }

            if (rule.paramOverrides) {
                scope.addDiag(diag::ConfigParamsIgnored, rule.paramOverrides->sourceRange())
                    << result->name;
            }

            return {{&topCells[0].definition, result, topCells[0].rule}, true};
        }
    }

    // Otherwise we have an error.
    errorMissingDef(id.name, *root, id.sourceRange, diag::UnknownModule);
    return {{}, true};
}

std::pair<Compilation::DefinitionLookupResult, bool> Compilation::resolveConfigRules(
    std::string_view lookupName, const Scope& scope, const ResolvedConfig* parentConfig,
    const ConfigRule* rule, const std::vector<Symbol*>& defList) const {

    const ConfigBlockSymbol::CellOverride* cellOverride = nullptr;
    std::span<const SourceLibrary* const> liblist;
    if (parentConfig) {
        SLANG_ASSERT(!rule);
        liblist = parentConfig->liblist;

        auto& conf = parentConfig->useConfig;
        auto& overrides = conf.getCellOverrides();
        if (auto overrideIt = overrides.find(lookupName); overrideIt != overrides.end()) {
            cellOverride = &overrideIt->second;
            rule = cellOverride->defaultRule;
        }
    }

    if (rule) {
        if (auto& id = rule->useCell; !id.name.empty())
            return resolveConfigRule(scope, *rule);

        rule->isUsed = true;
        if (rule->liblist)
            liblist = *rule->liblist;
    }

    auto findDefWithOverride = [&](const SourceLibrary& targetLib)
        -> std::optional<std::pair<Compilation::DefinitionLookupResult, bool>> {
        // If we have a cell override that specifically targets
        // this lib then we should just return that directly.
        if (cellOverride) {
            if (auto it = cellOverride->specificLibRules.find(&targetLib);
                it != cellOverride->specificLibRules.end()) {
                return resolveConfigRule(scope, *it->second);
            }
        }

        // Otherwise try to find the def in our list.
        if (auto def = findDefByLib(defList, targetLib)) {
            return std::pair<Compilation::DefinitionLookupResult, bool>{{def, nullptr, rule},
                                                                        false};
        }
        return std::nullopt;
    };

    if (!liblist.empty()) {
        // This search is O(n^2) but both lists should be small
        // (or even just one element each) in basically all cases.
        for (auto lib : liblist) {
            if (auto result = findDefWithOverride(*lib))
                return *result;
        }
    }
    else if (auto parentDef = scope.asSymbol().getDeclaringDefinition()) {
        // Fall back to picking based on the parent instance's library.
        if (auto result = findDefWithOverride(parentDef->sourceLibrary))
            return *result;
    }

    return {{}, false};
}

Diagnostic* Compilation::errorMissingDef(std::string_view name, const Scope& scope,
                                         SourceRange sourceRange, DiagCode code) const {
    if (hasFlag(CompilationFlags::IgnoreUnknownModules) || scope.isUninstantiated() || name.empty())
        return nullptr;

    if (auto def = getExternDefinition(name, scope)) {
        auto& diag = scope.addDiag(diag::MissingExternModuleImpl, getExternNameToken(*def).range());
        if (def->kind == SyntaxKind::ExternModuleDecl)
            diag << def->as<ExternModuleDeclSyntax>().header->moduleKeyword.valueText();
        else
            diag << "primitive"sv;

        diag << name;
        diag.addNote(diag::NoteReferencedHere, sourceRange);
        return &diag;
    }

    auto& diag = scope.addDiag(code, sourceRange) << name;
    return &diag;
}

} // namespace slang::ast
