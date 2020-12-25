//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Definition.h"
#include "slang/compilation/ScriptSession.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/types/TypePrinter.h"

namespace {

static const string_view DefinitionKindStrs[3] = { "module"sv, "interface"sv, "program"sv };

using namespace slang;

// This visitor is used to touch every node in the AST to ensure that all lazily
// evaluated members have been realized and we have recorded every diagnostic.
struct DiagnosticVisitor : public ASTVisitor<DiagnosticVisitor, false, false> {
    DiagnosticVisitor(Compilation& compilation, const size_t& numErrors, uint32_t errorLimit) :
        compilation(compilation), numErrors(numErrors), errorLimit(errorLimit) {}

    template<typename T>
    void handle(const T& symbol) {
        handleDefault(symbol);
    }

    template<typename T>
    bool handleDefault(const T& symbol) {
        if (numErrors > errorLimit)
            return false;

        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto declaredType = symbol.getDeclaredType();
            if (declaredType) {
                declaredType->getType();
                declaredType->getInitializer();
            }

            if constexpr (std::is_same_v<ParameterSymbol, T> ||
                          std::is_same_v<EnumValueSymbol, T>) {
                symbol.getValue();
            }

            for (auto attr : compilation.getAttributes(symbol))
                attr->getValue();
        }

        if constexpr (is_detected_v<getBody_t, T>)
            symbol.getBody().visit(*this);

        visitDefault(symbol);
        return true;
    }

    void handle(const ExplicitImportSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.importedSymbol();
    }

    void handle(const WildcardImportSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getPackage();
    }

    void handle(const ContinuousAssignSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.getAssignment();
    }

    void handle(const ElabSystemTaskSymbol& symbol) {
        if (!handleDefault(symbol))
            return;
        symbol.issueDiagnostic();
    }

    void handle(const MethodPrototypeSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        if (auto sub = symbol.getSubroutine())
            handle(*sub);
    }

    void handle(const GenericClassDefSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        // Save this for later; we need to revist all generic classes
        // once we've finished checking everything else.
        genericClasses.append(&symbol);
    }

    void handle(const NetType& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDataType();
    }

    void handle(const NetSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getDelay();
    }

    void handle(const ConstraintBlockSymbol& symbol) {
        if (!handleDefault(symbol))
            return;

        symbol.getConstraints();
    }

    void handle(const InstanceSymbol& symbol) {
        if (numErrors > errorLimit)
            return;

        instanceCount[&symbol.getDefinition()]++;
        symbol.resolvePortConnections();
        for (auto attr : compilation.getAttributes(symbol))
            attr->getValue();

        // Instance bodies are all the same, so if we've visited this one
        // already don't bother doing it again.
        if (!visitedInstanceBodies.emplace(&symbol.body).second)
            return;

        // In order to avoid infinitely recursive instantiations, keep track
        // of how deep we are in the hierarchy tree and report an error if we
        // get too deep.
        if (hierarchyDepth > compilation.getOptions().maxInstanceDepth) {
            auto& diag =
                symbol.getParentScope()->addDiag(diag::MaxInstanceDepthExceeded, symbol.location);
            diag << DefinitionKindStrs[int(symbol.getDefinition().definitionKind)];
            diag << compilation.getOptions().maxInstanceDepth;
            return;
        }

        hierarchyDepth++;
        visit(symbol.body);
        hierarchyDepth--;
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (!symbol.isInstantiated)
            return;
        handleDefault(symbol);
    }

    void finalize() {
        // Once everything has been visited, go back over and check things that might
        // have been influenced by visiting later symbols. Unfortunately visiting
        // a specialization can trigger more specializations to be made for the
        // same or other generic classs, so we need to be careful here when iterating.
        SmallSet<const Type*, 8> visitedSpecs;
        SmallVectorSized<const Type*, 8> toVisit;
        bool didSomething;
        do {
            didSomething = false;
            for (auto symbol : genericClasses) {
                for (auto& spec : symbol->specializations()) {
                    if (visitedSpecs.emplace(&spec).second)
                        toVisit.append(&spec);
                }

                for (auto spec : toVisit) {
                    spec->visit(*this);
                    didSomething = true;
                }

                toVisit.clear();
            }
        } while (didSomething);

        // Go back over and find generic classes that were never instantiated
        // and force an empty one to make sure we collect all diagnostics that
        // don't depend on parameter values.
        for (auto symbol : genericClasses) {
            if (symbol->numSpecializations() == 0)
                symbol->getInvalidSpecialization().visit(*this);
        }
    }

    Compilation& compilation;
    const size_t& numErrors;
    flat_hash_map<const Definition*, size_t> instanceCount;
    flat_hash_set<const InstanceBodySymbol*> visitedInstanceBodies;
    uint32_t errorLimit;
    uint32_t hierarchyDepth = 0;
    SmallVectorSized<const GenericClassDefSymbol*, 8> genericClasses;
};

// This visitor is for finding all bind directives in the hierarchy.
struct BindVisitor : public ASTVisitor<BindVisitor, false, false> {
    BindVisitor(const flat_hash_set<const BindDirectiveSyntax*>& foundDirectives, size_t expected) :
        foundDirectives(foundDirectives), expected(expected) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }

    void handle(const CompilationUnitSymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;
        visitDefault(symbol);
    }

    void handle(const InstanceSymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;

        if (!visitedInstances.emplace(&symbol.body).second) {
            errored = true;
            return;
        }

        visitDefault(symbol.body);
    }

    void handle(const GenerateBlockSymbol& symbol) {
        if (foundDirectives.size() == expected || !symbol.isInstantiated)
            return;
        visitDefault(symbol);
    }

    void handle(const GenerateBlockArraySymbol& symbol) {
        if (foundDirectives.size() == expected)
            return;

        auto members = symbol.members();
        if (members.begin() == members.end())
            return;

        visit(*members.begin());
    }

    template<typename T>
    void handle(const T&) {}

    const flat_hash_set<const BindDirectiveSyntax*>& foundDirectives;
    flat_hash_set<const InstanceBodySymbol*> visitedInstances;
    size_t expected;
    bool errored = false;
};

} // namespace

namespace slang::Builtins {

void registerArrayMethods(Compilation&);
void registerConversionFuncs(Compilation&);
void registerEnumMethods(Compilation&);
void registerMathFuncs(Compilation&);
void registerMiscSystemFuncs(Compilation&);
void registerNonConstFuncs(Compilation&);
void registerQueryFuncs(Compilation&);
void registerStringMethods(Compilation&);
void registerSystemTasks(Compilation&);
const PackageSymbol& createStdPackage(Compilation&);

} // namespace slang::Builtins

namespace slang {

Compilation::Compilation(const Bag& options) :
    options(options.getOrDefault<CompilationOptions>()), tempDiag({}, {}) {

    // Construct all built-in types.
    bitType = emplace<ScalarType>(ScalarType::Bit);
    logicType = emplace<ScalarType>(ScalarType::Logic);
    regType = emplace<ScalarType>(ScalarType::Reg);
    signedBitType = emplace<ScalarType>(ScalarType::Bit, true);
    signedLogicType = emplace<ScalarType>(ScalarType::Logic, true);
    signedRegType = emplace<ScalarType>(ScalarType::Reg, true);
    shortIntType = emplace<PredefinedIntegerType>(PredefinedIntegerType::ShortInt);
    intType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Int);
    longIntType = emplace<PredefinedIntegerType>(PredefinedIntegerType::LongInt);
    byteType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Byte);
    integerType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Integer);
    timeType = emplace<PredefinedIntegerType>(PredefinedIntegerType::Time);
    realType = emplace<FloatingType>(FloatingType::Real);
    realTimeType = emplace<FloatingType>(FloatingType::RealTime);
    shortRealType = emplace<FloatingType>(FloatingType::ShortReal);
    stringType = emplace<StringType>();
    chandleType = emplace<CHandleType>();
    voidType = emplace<VoidType>();
    nullType = emplace<NullType>();
    eventType = emplace<EventType>();
    errorType = emplace<ErrorType>();

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
    knownTypes[SyntaxKind::VoidType] = voidType;
    knownTypes[SyntaxKind::EventType] = eventType;
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

    knownNetTypes[TokenKind::Unknown] =
        std::make_unique<NetType>(NetType::Unknown, "<error>", *logicType);
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

    defaultTimeScale.base = { TimeUnit::Nanoseconds, TimeScaleMagnitude::One };
    defaultTimeScale.precision = { TimeUnit::Nanoseconds, TimeScaleMagnitude::One };

    root = std::make_unique<RootSymbol>(*this);
    instanceCache = std::make_unique<InstanceCache>();

    // Register all system tasks, functions, and methods.
    Builtins::registerArrayMethods(*this);
    Builtins::registerConversionFuncs(*this);
    Builtins::registerEnumMethods(*this);
    Builtins::registerMathFuncs(*this);
    Builtins::registerMiscSystemFuncs(*this);
    Builtins::registerNonConstFuncs(*this);
    Builtins::registerQueryFuncs(*this);
    Builtins::registerStringMethods(*this);
    Builtins::registerSystemTasks(*this);

    // Register the built-in std package.
    stdPkg = &Builtins::createStdPackage(*this);
    packageMap.emplace(stdPkg->name, stdPkg);

    // Set a default handler for printing types and symbol paths, for convenience.
    DiagnosticEngine::setDefaultFormatter<const Type*>(std::make_unique<TypeArgFormatter>());
    TextDiagnosticClient::setDefaultSymbolPathCB([](const Symbol& sym) {
        std::string str;
        sym.getHierarchicalPath(str);
        return str;
    });

    // Reset systemId counters that may have been changed due to creation of types
    // in the std package.
    nextEnumSystemId = 1;
    nextStructSystemId = 1;
    nextUnionSystemId = 1;
}

Compilation::~Compilation() = default;
Compilation::Compilation(Compilation&&) = default;

void Compilation::addSyntaxTree(std::shared_ptr<SyntaxTree> tree) {
    if (finalized)
        throw std::logic_error("The compilation has already been finalized");

    if (&tree->sourceManager() != sourceManager) {
        if (!sourceManager)
            sourceManager = &tree->sourceManager();
        else {
            throw std::logic_error(
                "All syntax trees added to the compilation must use the same source manager");
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
        auto decl = &n->as<ModuleDeclarationSyntax>();
        DefinitionMetadata result;
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

        definitionMetadata[decl] = result;
    }

    for (auto& name : tree->getMetadata().globalInstances)
        globalInstantiations.emplace(name);

    if (node.kind == SyntaxKind::CompilationUnit) {
        for (auto member : node.as<CompilationUnitSyntax>().members)
            unit->addMembers(*member);
    }
    else {
        unit->addMembers(node);
    }

    syntaxTrees.emplace_back(std::move(tree));
    cachedParseDiagnostics.reset();
}

span<const std::shared_ptr<SyntaxTree>> Compilation::getSyntaxTrees() const {
    return syntaxTrees;
}

span<const CompilationUnitSymbol* const> Compilation::getCompilationUnits() const {
    return compilationUnits;
}

const RootSymbol& Compilation::getRoot() {
    if (finalized)
        return *root;

    // If any top-level parameter overrides were provided, parse them now.
    flat_hash_map<string_view, const ConstantValue*> paramOverrides;
    parseParamOverrides(paramOverrides);

    ASSERT(!finalizing);
    finalizing = true;
    auto guard = ScopeGuard([this] { finalizing = false; });

    auto isValidTop = [&](auto& definition) {
        // All parameters must have defaults.
        for (auto& param : definition.parameters) {
            if (!param.hasDefault() && paramOverrides.find(param.name) == paramOverrides.end())
                return false;
        }

        // Can't have interface ports.
        for (auto& port : definition.getPorts()) {
            if (port.likelyInterface)
                return false;
        }

        return true;
    };

    // Find top level modules that form the root of the design. Iterate the definitions
    // map before instantiating any top level modules, since that can cause changes
    // to the definition map itself.
    SmallVectorSized<const Definition*, 8> topDefs;
    if (options.topModules.empty()) {
        for (auto& [key, definition] : definitionMap) {
            // Ignore definitions that are not top level. Top level definitions are:
            // - Always modules
            // - Not nested
            // - Have no non-defaulted parameters
            // - Not instantiated anywhere
            if (std::get<1>(key) != root.get() ||
                globalInstantiations.find(definition->name) != globalInstantiations.end()) {
                continue;
            }

            if (definition->definitionKind == DefinitionKind::Module) {
                if (isValidTop(*definition)) {
                    // This module can be automatically instantiated.
                    topDefs.append(definition.get());
                    continue;
                }
            }

            // Otherwise this definition is unreferenced and not automatically instantiated.
            unreferencedDefs.push_back(definition.get());
        }
    }
    else {
        // If the list of top modules has already been provided we just need to
        // find and instantiate them.
        auto& tm = options.topModules;
        for (auto& [key, definition] : definitionMap) {
            if (std::get<1>(key) != root.get())
                continue;

            if (definition->definitionKind == DefinitionKind::Module) {
                if (auto it = tm.find(definition->name); it != tm.end()) {
                    // Remove from the top modules set so that we know we visited it.
                    tm.erase(it);

                    // Make sure this is actually valid as a top-level module.
                    if (isValidTop(*definition)) {
                        topDefs.append(definition.get());
                        continue;
                    }

                    // Otherwise, issue an error because the user asked us to instantiate this.
                    definition->scope.addDiag(diag::InvalidTopModule, SourceLocation::NoLocation)
                        << definition->name;
                    continue;
                }
            }

            // Otherwise this definition might be unreferenced and not automatically instantiated.
            if (globalInstantiations.find(definition->name) == globalInstantiations.end())
                unreferencedDefs.push_back(definition.get());
        }

        // If any top modules were not found, issue an error.
        for (auto& name : tm)
            root->addDiag(diag::InvalidTopModule, SourceLocation::NoLocation) << name;
    }

    // Sort the list of definitions so that we get deterministic ordering of instances;
    // the order is otherwise dependent on iterating over a hash table.
    auto byName = [](auto a, auto b) { return a->name < b->name; };
    std::sort(topDefs.begin(), topDefs.end(), byName);
    std::sort(unreferencedDefs.begin(), unreferencedDefs.end(), byName);

    SmallVectorSized<const InstanceSymbol*, 4> topList;
    for (auto def : topDefs) {
        auto& instance = InstanceSymbol::createDefault(*this, *def, &paramOverrides);
        root->addMember(instance);
        topList.append(&instance);
    }

    if (!options.suppressUnused && topDefs.empty())
        root->addDiag(diag::NoTopModules, SourceLocation::NoLocation);

    // For unreferenced definitions, go through and instantiate them with all empty
    // parameter values so that we get at least some semantic checking of the contents.
    for (auto def : unreferencedDefs)
        root->addMember(InstanceSymbol::createInvalid(*this, *def));

    root->topInstances = topList.copy(*this);
    root->compilationUnits = compilationUnits;
    finalizing = false;
    finalized = true;

    // If there are any bind directives in the design, we need to opportunistically
    // traverse the hierarchy now to find them (because they can modify the hierarchy and
    // accessing other nodes / expressions might not be valid without those bound
    // instances present).
    size_t numBinds = 0;
    for (auto& tree : syntaxTrees)
        numBinds += tree->getMetadata().bindDirectives.size();

    if (numBinds) {
        BindVisitor visitor(seenBindDirectives, numBinds);
        root->visit(visitor);
        ASSERT(visitor.errored || seenBindDirectives.size() == numBinds);
    }

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

const Definition* Compilation::getDefinition(string_view lookupName, const Scope& scope) const {
    // First try to do a quick lookup in the top definitions map (most definitions are global).
    // If the flag is set it means we have to do a full scope lookup instead.
    if (auto it = topDefinitions.find(lookupName); it != topDefinitions.end()) {
        if (!it->second.second)
            return it->second.first;
    }

    // There are nested modules somewhere with this same name, so we need to do the full search.
    const Scope* searchScope = &scope;
    while (searchScope) {
        auto it = definitionMap.find(std::make_tuple(lookupName, searchScope));
        if (it != definitionMap.end())
            return it->second.get();

        auto& sym = searchScope->asSymbol();
        if (sym.kind == SymbolKind::Root)
            return nullptr;

        searchScope = sym.getParentScope();
    }

    return nullptr;
}

const Definition* Compilation::getDefinition(string_view lookupName) const {
    return getDefinition(lookupName, *root);
}

const Definition* Compilation::getDefinition(const ModuleDeclarationSyntax& syntax) const {
    for (auto& [key, def] : definitionMap) {
        if (&def->syntax == &syntax)
            return def.get();
    }
    return nullptr;
}

const Definition& Compilation::createDefinition(const Scope& scope, LookupLocation location,
                                                const ModuleDeclarationSyntax& syntax) {
    auto& metadata = definitionMetadata[&syntax];
    auto def = std::make_unique<Definition>(scope, location, syntax, *metadata.defaultNetType,
                                            metadata.unconnectedDrive, metadata.timeScale);

    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    auto it = definitionMap.emplace(std::tuple(def->name, targetScope), std::move(def)).first;

    auto result = it->second.get();
    if (targetScope == root.get()) {
        auto& topDef = topDefinitions[result->name].first;
        if (topDef) {
            auto& diag = scope.addDiag(diag::Redefinition, result->location);
            diag << result->name;
            diag.addNote(diag::NotePreviousDefinition, topDef->location);
        }
        else {
            topDef = result;
        }
    }
    else {
        // Record the fact that we have nested modules with this given name.
        topDefinitions[result->name].second = true;
    }

    return *result;
}

const PackageSymbol* Compilation::getPackage(string_view lookupName) const {
    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;
    return it->second;
}

const PackageSymbol& Compilation::createPackage(const Scope& scope,
                                                const ModuleDeclarationSyntax& syntax) {
    auto& metadata = definitionMetadata[&syntax];
    auto& package =
        PackageSymbol::fromSyntax(scope, syntax, *metadata.defaultNetType, metadata.timeScale);

    auto [it, inserted] = packageMap.emplace(package.name, &package);
    if (!inserted) {
        auto& diag = scope.addDiag(diag::Redefinition, package.location);
        diag << package.name;
        diag.addNote(diag::NotePreviousDefinition, it->second->location);
    }

    return package;
}

void Compilation::addSystemSubroutine(std::unique_ptr<SystemSubroutine> subroutine) {
    subroutineMap.emplace(subroutine->name, std::move(subroutine));
}

void Compilation::addSystemMethod(SymbolKind typeKind, std::unique_ptr<SystemSubroutine> method) {
    methodMap.emplace(std::make_tuple(string_view(method->name), typeKind), std::move(method));
}

const SystemSubroutine* Compilation::getSystemSubroutine(string_view name) const {
    auto it = subroutineMap.find(name);
    if (it == subroutineMap.end())
        return nullptr;
    return it->second.get();
}

const SystemSubroutine* Compilation::getSystemMethod(SymbolKind typeKind, string_view name) const {
    auto it = methodMap.find(std::make_tuple(name, typeKind));
    if (it == methodMap.end())
        return nullptr;
    return it->second.get();
}

void Compilation::setAttributes(const Symbol& symbol,
                                span<const AttributeSymbol* const> attributes) {
    attributeMap[&symbol] = attributes;
}

void Compilation::setAttributes(const Statement& stmt,
                                span<const AttributeSymbol* const> attributes) {
    attributeMap[&stmt] = attributes;
}

void Compilation::setAttributes(const Expression& expr,
                                span<const AttributeSymbol* const> attributes) {
    attributeMap[&expr] = attributes;
}

span<const AttributeSymbol* const> Compilation::getAttributes(const Symbol& symbol) const {
    return getAttributes(static_cast<const void*>(&symbol));
}

span<const AttributeSymbol* const> Compilation::getAttributes(const Statement& stmt) const {
    return getAttributes(static_cast<const void*>(&stmt));
}

span<const AttributeSymbol* const> Compilation::getAttributes(const Expression& expr) const {
    return getAttributes(static_cast<const void*>(&expr));
}

span<const AttributeSymbol* const> Compilation::getAttributes(const void* ptr) const {
    auto it = attributeMap.find(ptr);
    if (it == attributeMap.end())
        return {};

    return it->second;
}

void Compilation::addInstance(const InstanceSymbol& instance) {
    instanceParents[&instance.body].push_back(&instance);
}

span<const InstanceSymbol* const> Compilation::getParentInstances(
    const InstanceBodySymbol& body) const {
    auto it = instanceParents.find(&body);
    if (it == instanceParents.end())
        return {};
    return it->second;
}

void Compilation::noteInterfacePort(const Definition& definition) {
    usedIfacePorts.emplace(&definition);
}

bool Compilation::noteBindDirective(const BindDirectiveSyntax& syntax,
                                    const Definition* targetDef) {
    if (!seenBindDirectives.emplace(&syntax).second)
        return false;

    if (targetDef)
        bindDirectivesByDef[targetDef].push_back(&syntax);

    return true;
}

void Compilation::addOutOfBlockDecl(const Scope& scope, const ScopedNameSyntax& name,
                                    const SyntaxNode& syntax, SymbolIndex index) {
    string_view className = name.left->getLastToken().valueText();
    string_view declName = name.right->getLastToken().valueText();
    outOfBlockDecls.emplace(std::make_tuple(className, declName, &scope),
                            std::make_tuple(&syntax, &name, index, false));
}

std::tuple<const SyntaxNode*, SymbolIndex, bool*> Compilation::findOutOfBlockDecl(
    const Scope& scope, string_view className, string_view declName) const {

    auto it = outOfBlockDecls.find({ className, declName, &scope });
    if (it != outOfBlockDecls.end()) {
        auto& [syntax, name, index, used] = it->second;
        return { syntax, index, &used };
    }

    return { nullptr, SymbolIndex(), nullptr };
}

const NameSyntax& Compilation::parseName(string_view name) {
    Diagnostics localDiags;
    auto& result = tryParseName(name, localDiags);

    if (!localDiags.empty()) {
        SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
        localDiags.sort(sourceMan);
        throw std::runtime_error(DiagnosticEngine::reportAll(sourceMan, localDiags));
    }

    return result;
}

const NameSyntax& Compilation::tryParseName(string_view name, Diagnostics& localDiags) {
    SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
    Preprocessor preprocessor(sourceMan, *this, localDiags);
    preprocessor.pushSource(sourceMan.assignText(name));

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
        cachedParseDiagnostics->appendRange(tree->diagnostics());

    if (sourceManager)
        cachedParseDiagnostics->sort(*sourceManager);
    return *cachedParseDiagnostics;
}

const Diagnostics& Compilation::getSemanticDiagnostics() {
    if (cachedSemanticDiagnostics)
        return *cachedSemanticDiagnostics;

    // If we haven't already done so, touch every symbol, scope, statement,
    // and expression tree so that we can be sure we have all the diagnostics.
    DiagnosticVisitor visitor(*this, numErrors,
                              options.errorLimit == 0 ? UINT32_MAX : options.errorLimit);
    getRoot().visit(visitor);
    visitor.finalize();

    // Report on unused out-of-block definitions. These are always a real error.
    for (auto& [key, val] : outOfBlockDecls) {
        auto& [syntax, name, index, used] = val;
        if (!used) {
            auto& [className, declName, scope] = key;
            auto classRange = name->left->sourceRange();
            auto sym = Lookup::unqualifiedAt(*scope, className,
                                             LookupLocation(scope, uint32_t(index)), classRange);

            if (sym) {
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

    // Report on unused definitions.
    if (!options.suppressUnused) {
        for (auto def : unreferencedDefs) {
            // If this is an interface, it may have been referenced in a port.
            if (usedIfacePorts.find(def) != usedIfacePorts.end())
                continue;

            def->scope.addDiag(diag::UnusedDefinition, def->location)
                << DefinitionKindStrs[int(def->definitionKind)];
        }
    }

    Diagnostics results;
    for (auto& [key, diagList] : diagMap) {
        // If the location is NoLocation, just issue each diagnostic.
        if (std::get<1>(key) == SourceLocation::NoLocation) {
            for (auto& diag : diagList)
                results.emplace(diag);
            continue;
        }

        // Try to find a diagnostic in an instance that isn't at the top-level
        // (printing such a path seems silly).
        const Diagnostic* found = nullptr;
        const Symbol* inst = nullptr;
        size_t count = 0;

        for (auto& diag : diagList) {
            auto symbol = diag.symbol;
            while (symbol && symbol->kind != SymbolKind::InstanceBody) {
                auto scope = symbol->getParentScope();
                symbol = scope ? &scope->asSymbol() : nullptr;
            }

            if (!symbol)
                continue;

            auto parents = getParentInstances(symbol->as<InstanceBodySymbol>());
            if (parents.empty())
                continue;

            count += parents.size();
            for (auto parent : parents) {
                if (auto scope = parent->getParentScope()) {
                    auto& sym = scope->asSymbol();
                    if (sym.kind != SymbolKind::Root && sym.kind != SymbolKind::CompilationUnit) {
                        found = &diag;
                        inst = parent;
                    }
                }
            }
        }

        // If the diagnostic is present in all instances, don't bother
        // providing specific instantiation info.
        if (found && visitor.instanceCount[&inst->as<InstanceSymbol>().getDefinition()] > count) {
            Diagnostic diag = *found;
            diag.symbol = inst;
            diag.coalesceCount = count;
            results.emplace(std::move(diag));
        }
        else {
            results.emplace(diagList.front());
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
    cachedAllDiagnostics->appendRange(getParseDiagnostics());
    cachedAllDiagnostics->appendRange(getSemanticDiagnostics());

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
            if (symbol->kind == SymbolKind::GenerateBlock &&
                !symbol->as<GenerateBlockSymbol>().isInstantiated)
                return true;

            auto scope = symbol->getParentScope();
            symbol = scope ? &scope->asSymbol() : nullptr;
        }
        return false;
    };

    // Filter out diagnostics that came from inside an uninstantiated generate block.
    ASSERT(diag.symbol);
    ASSERT(diag.location);
    if (isSuppressed(diag.symbol)) {
        tempDiag = std::move(diag);
        return tempDiag;
    }

    // Coalesce diagnostics that are at the same source location and have the same code.
    if (auto it = diagMap.find({ diag.code, diag.location }); it != diagMap.end()) {
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

const Type& Compilation::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? *errorType : *it->second;
}

const Type& Compilation::getType(const DataTypeSyntax& node, LookupLocation location,
                                 const Scope& parent, const Type* typedefTarget) {
    return Type::fromSyntax(*this, node, location, parent, typedefTarget);
}

const Type& Compilation::getType(const Type& elementType,
                                 const SyntaxList<VariableDimensionSyntax>& dimensions,
                                 LookupLocation location, const Scope& scope) {
    return Type::fromSyntax(*this, elementType, dimensions, location, scope);
}

const Type& Compilation::getType(bitwidth_t width, bitmask<IntegralFlags> flags) {
    ASSERT(width > 0 && width <= SVInt::MAX_BITS);
    uint32_t key = width;
    key |= uint32_t(flags.bits()) << SVInt::BITWIDTH_BITS;
    auto it = vectorTypeCache.find(key);
    if (it != vectorTypeCache.end())
        return *it->second;

    auto type =
        emplace<PackedArrayType>(getScalarType(flags), ConstantRange{ int32_t(width - 1), 0 });
    vectorTypeCache.emplace_hint(it, key, type);
    return *type;
}

const Type& Compilation::getScalarType(bitmask<IntegralFlags> flags) {
    Type* ptr = scalarTypeTable[flags.bits() & 0x7];
    ASSERT(ptr);
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

InstanceCache& Compilation::getInstanceCache() {
    return *instanceCache;
}

const InstanceCache& Compilation::getInstanceCache() const {
    return *instanceCache;
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
        return {};
    return importData[index];
}

void Compilation::parseParamOverrides(flat_hash_map<string_view, const ConstantValue*>& results) {
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
            string_view optView = opt;
            string_view name = optView.substr(0, index);
            if (tryParseName(name, localDiags).kind == SyntaxKind::IdentifierName &&
                localDiags.empty()) {

                // The name is good, evaluate the value string. Using the ScriptSession
                // here is a little bit lazy but oh well, this executes almost never
                // compared to everything else during compilation.
                string_view value = optView.substr(index + 1);
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

} // namespace slang
