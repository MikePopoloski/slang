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

#include "slang/ast/Definition.h"
#include "slang/ast/ScriptSession.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
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
    options(options.getOrDefault<CompilationOptions>()), tempDiag({}, {}) {

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

    defaultTimeScale.base = {TimeUnit::Nanoseconds, TimeScaleMagnitude::One};
    defaultTimeScale.precision = {TimeUnit::Nanoseconds, TimeScaleMagnitude::One};

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
    return getRoot(/* skipDefParamResolution */ false);
}

const RootSymbol& Compilation::getRoot(bool skipDefParamResolution) {
    if (finalized)
        return *root;

    // If any top-level parameter overrides were provided, parse them now.
    flat_hash_map<string_view, const ConstantValue*> cliOverrides;
    parseParamOverrides(cliOverrides);

    // If there are defparams we need to fully resolve their values up front before
    // we start elaborating any instances.
    size_t numDefParams = 0, numBinds = 0;
    for (auto& tree : syntaxTrees) {
        auto& meta = tree->getMetadata();
        numDefParams += meta.defparams.size();
        numBinds += meta.bindDirectives.size();
    }

    if (!skipDefParamResolution && numDefParams)
        resolveDefParams(numDefParams);

    ASSERT(!finalizing);
    finalizing = true;
    auto guard = ScopeGuard([this] { finalizing = false; });

    auto isValidTop = [&](auto& definition) {
        // All parameters must have defaults.
        for (auto& param : definition.parameters) {
            if (!param.hasDefault() && cliOverrides.find(param.name) == cliOverrides.end())
                return false;
        }
        return true;
    };

    // Find top level modules that form the root of the design. Iterate the definitions
    // map before instantiating any top level modules, since that can cause changes
    // to the definition map itself.
    SmallVector<const Definition*> topDefs;
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

            // Library modules are never automatically instantiated in any capacity.
            if (!definition->syntaxTree || !definition->syntaxTree->isLibrary) {
                if (definition->definitionKind == DefinitionKind::Module) {
                    if (isValidTop(*definition)) {
                        // This module can be automatically instantiated.
                        topDefs.push_back(definition.get());
                        continue;
                    }
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
                        topDefs.push_back(definition.get());
                        continue;
                    }

                    // Otherwise, issue an error because the user asked us to instantiate this.
                    definition->scope.addDiag(diag::InvalidTopModule, SourceLocation::NoLocation)
                        << definition->name;
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

    // If we have any cli param overrides we should apply them to
    // each top-level instance.
    if (!cliOverrides.empty()) {
        for (auto def : topDefs) {
            auto& node = paramOverrides.childNodes[std::string(def->name)];
            for (auto [name, value] : cliOverrides)
                node.overrides.emplace(std::string(name), *value);
        }
    }

    SmallVector<const InstanceSymbol*> topList;
    for (auto def : topDefs) {
        const ParamOverrideNode* paramOverrideNode = nullptr;
        if (!paramOverrides.childNodes.empty()) {
            if (auto it = paramOverrides.childNodes.find(std::string(def->name));
                it != paramOverrides.childNodes.end()) {
                paramOverrideNode = &it->second;
            }
        }

        auto& instance = InstanceSymbol::createDefault(*this, *def, paramOverrideNode);
        root->addMember(instance);
        topList.push_back(&instance);
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
    if (numBinds) {
        BindVisitor visitor(seenBindDirectives, numBinds);
        root->visit(visitor);
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
    do {
        auto it = definitionMap.find(std::make_tuple(lookupName, searchScope));
        if (it != definitionMap.end())
            return it->second.get();

        searchScope = searchScope->asSymbol().getParentScope();
    } while (searchScope);

    return nullptr;
}

const Definition* Compilation::getDefinition(const ModuleDeclarationSyntax& syntax) const {
    for (auto& [key, def] : definitionMap) {
        if (&def->syntax == &syntax)
            return def.get();
    }
    return nullptr;
}

template<typename T, typename U>
static void reportRedefinition(const Scope& scope, const T& newSym, const U& oldSym,
                               DiagCode code = diag::Redefinition) {
    if (!newSym.name.empty()) {
        auto& diag = scope.addDiag(code, newSym.location);
        diag << newSym.name;
        diag.addNote(diag::NotePreviousDefinition, oldSym.location);
    }
}

void Compilation::createDefinition(const Scope& scope, LookupLocation location,
                                   const ModuleDeclarationSyntax& syntax) {
    auto& metadata = definitionMetadata[&syntax];
    auto def = std::make_unique<Definition>(scope, location, syntax, *metadata.defaultNetType,
                                            metadata.unconnectedDrive, metadata.timeScale,
                                            metadata.tree);

    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    auto targetScope = scope.asSymbol().kind == SymbolKind::CompilationUnit ? root.get() : &scope;
    std::tuple key(def->name, targetScope);
    if (auto it = definitionMap.find(key); it != definitionMap.end())
        reportRedefinition(scope, *def, *it->second, diag::DuplicateDefinition);

    const auto& result = (definitionMap[key] = std::move(def));
    if (targetScope == root.get()) {
        topDefinitions[result->name].first = result.get();
        if (auto primIt = udpMap.find(result->name); primIt != udpMap.end())
            reportRedefinition(scope, *result, *primIt->second);
    }
    else {
        // Record the fact that we have nested modules with this given name.
        topDefinitions[result->name].second = true;
    }
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
    auto& package = PackageSymbol::fromSyntax(scope, syntax, *metadata.defaultNetType,
                                              metadata.timeScale);

    auto [it, inserted] = packageMap.emplace(package.name, &package);
    if (!inserted && !package.name.empty()) {
        auto& diag = scope.addDiag(diag::Redefinition, package.location);
        diag << package.name;
        diag.addNote(diag::NotePreviousDefinition, it->second->location);
    }

    return package;
}

const PrimitiveSymbol* Compilation::getPrimitive(string_view lookupName) const {
    if (auto it = udpMap.find(lookupName); it != udpMap.end())
        return it->second;
    return nullptr;
}

const PrimitiveSymbol& Compilation::createPrimitive(const Scope& scope,
                                                    const UdpDeclarationSyntax& syntax) {
    auto& prim = PrimitiveSymbol::fromSyntax(scope, syntax);
    if (!prim.name.empty()) {
        if (auto ps = getPrimitive(prim.name))
            reportRedefinition(*root, prim, *ps, diag::DuplicateDefinition);
        else if (auto defIt = topDefinitions.find(prim.name); defIt != topDefinitions.end()) {
            reportRedefinition(*root, prim, *defIt->second.first);
        }
        udpMap[prim.name] = &prim;
    }

    return prim;
}

const PrimitiveSymbol* Compilation::getGateType(string_view lookupName) const {
    if (auto it = gateMap.find(lookupName); it != gateMap.end())
        return it->second;
    return nullptr;
}

void Compilation::addGateType(const PrimitiveSymbol& prim) {
    ASSERT(!prim.name.empty());
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
    methodMap.emplace(std::make_tuple(string_view(method->name), typeKind), method.get());
    subroutineStorage.emplace_back(std::move(method));
}

void Compilation::addSystemMethod(SymbolKind typeKind, const SystemSubroutine& method) {
    methodMap.emplace(std::make_tuple(string_view(method.name), typeKind), &method);
}

const SystemSubroutine* Compilation::getSystemSubroutine(string_view name) const {
    auto it = subroutineMap.find(name);
    if (it == subroutineMap.end())
        return nullptr;
    return it->second;
}

const SystemSubroutine* Compilation::getSystemMethod(SymbolKind typeKind, string_view name) const {
    auto it = methodMap.find(std::make_tuple(name, typeKind));
    if (it == methodMap.end())
        return nullptr;
    return it->second;
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

void Compilation::setAttributes(const PortConnection& conn,
                                span<const AttributeSymbol* const> attributes) {
    attributeMap[&conn] = attributes;
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

span<const AttributeSymbol* const> Compilation::getAttributes(const PortConnection& conn) const {
    return getAttributes(static_cast<const void*>(&conn));
}

span<const AttributeSymbol* const> Compilation::getAttributes(const void* ptr) const {
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
                                                      string_view name) const {
    if (auto it = packageExportCandidateMap.find(&packageScope);
        it != packageExportCandidateMap.end()) {
        if (auto symIt = it->second.find(name); symIt != it->second.end())
            return symIt->second;
    }
    return nullptr;
}

bool Compilation::noteBindDirective(const BindDirectiveSyntax& syntax,
                                    const Definition* targetDef) {
    if (!seenBindDirectives.emplace(&syntax).second)
        return false;

    if (targetDef)
        bindDirectivesByDef[targetDef].push_back(&syntax);

    return true;
}

void Compilation::noteDPIExportDirective(const DPIExportSyntax& syntax, const Scope& scope) {
    dpiExports.emplace_back(&syntax, &scope);
}

void Compilation::addOutOfBlockDecl(const Scope& scope, const ScopedNameSyntax& name,
                                    const SyntaxNode& syntax, SymbolIndex index) {
    string_view className = name.left->getLastToken().valueText();
    string_view declName = name.right->getLastToken().valueText();
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
    const Scope& scope, string_view className, string_view declName) const {

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

        auto& sym = curr->asSymbol();
        if (sym.kind != SymbolKind::InstanceBody)
            curr = sym.getParentScope();
        else {
            auto parent = sym.as<InstanceBodySymbol>().parentInstance;
            ASSERT(parent);

            curr = parent->getParentScope();
        }
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
        cachedParseDiagnostics->append(tree->diagnostics());

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

    // Note for the following checks here: anything that depends on a list
    // stored in the compilation object should think carefully about taking
    // a copy of that list first before iterating over it, because your check
    // might trigger additional action that ends up adding to that list,
    // causing undefined behavior.

    // Check all DPI methods for correctness.
    if (!dpiExports.empty() || !visitor.dpiImports.empty())
        checkDPIMethods(visitor.dpiImports);

    // Check extern interface methods for correctness.
    if (!externInterfaceMethods.empty()) {
        auto methods = externInterfaceMethods;
        for (auto method : methods)
            method->connectExternInterfacePrototype();
    }

    if (!visitor.externIfaceProtos.empty())
        checkExternIfaceMethods(visitor.externIfaceProtos);

    if (!visitor.modportsWithExports.empty())
        checkModportExports(visitor.modportsWithExports);

    // Report any lingering name conflicts.
    if (!nameConflicts.empty()) {
        auto conflicts = nameConflicts;
        for (auto symbol : conflicts) {
            auto scope = symbol->getParentScope();
            ASSERT(scope);
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

    if (!options.suppressUnused) {
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

        // Report on unused definitions.
        for (auto def : unreferencedDefs) {
            // If this is an interface, it may have been referenced in a port.
            if (visitor.usedIfacePorts.find(def) != visitor.usedIfacePorts.end())
                continue;

            def->scope.addDiag(diag::UnusedDefinition, def->location) << def->getKindString();
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

        for (auto& diag : diagList) {
            auto symbol = diag.symbol;
            while (symbol && symbol->kind != SymbolKind::InstanceBody) {
                auto scope = symbol->getParentScope();
                symbol = scope ? &scope->asSymbol() : nullptr;
            }

            if (!symbol)
                continue;

            auto parent = symbol->as<InstanceBodySymbol>().parentInstance;
            ASSERT(parent);

            count++;
            if (auto scope = parent->getParentScope()) {
                auto& sym = scope->asSymbol();
                if (sym.kind != SymbolKind::Root && sym.kind != SymbolKind::CompilationUnit) {
                    found = &diag;
                    inst = parent;
                }
            }
        }

        // If the diagnostic is present in all instances, don't bother
        // providing specific instantiation info.
        if (found && visitor.instanceCount[&inst->as<InstanceSymbol>().getDefinition()] > count) {
            Diagnostic diag = *found;
            diag.symbol = inst;
            diag.coalesceCount = count;
            results.emplace_back(std::move(diag));
        }
        else {
            auto it = diagList.begin();
            ASSERT(it != diagList.end());

            results.emplace_back(*it);
            for (++it; it != diagList.end(); ++it) {
                if (*it != results.back())
                    results.emplace_back(*it);
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
    cachedAllDiagnostics->append(getParseDiagnostics());
    cachedAllDiagnostics->append(getSemanticDiagnostics());

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
    ASSERT(width > 0 && width <= SVInt::MAX_BITS);
    uint32_t key = width;
    key |= uint32_t(flags.bits()) << SVInt::BITWIDTH_BITS;
    auto it = vectorTypeCache.find(key);
    if (it != vectorTypeCache.end())
        return *it->second;

    auto type = emplace<PackedArrayType>(getScalarType(flags),
                                         ConstantRange{int32_t(width - 1), 0});
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

void Compilation::checkDPIMethods(span<const SubroutineSymbol* const> dpiImports) {
    auto getCId = [&](const Scope& scope, Token cid, Token name) {
        string_view text = cid ? cid.valueText() : name.valueText();
        if (!text.empty()) {
            auto tail = text.substr(1);
            if (!isValidCIdChar(text[0]) || isDecimalDigit(text[0]) ||
                std::any_of(tail.begin(), tail.end(), [](char c) { return !isValidCIdChar(c); })) {
                scope.addDiag(diag::InvalidDPICIdentifier, cid ? cid.range() : name.range())
                    << text;
                return string_view();
            }
        }
        return text;
    };

    flat_hash_map<string_view, const SubroutineSymbol*> nameMap;
    for (auto sub : dpiImports) {
        auto syntax = sub->getSyntax();
        ASSERT(syntax);

        auto scope = sub->getParentScope();
        ASSERT(scope);

        auto& dis = syntax->as<DPIImportSyntax>();
        string_view cId = getCId(*scope, dis.c_identifier, dis.method->name->getLastToken());
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

    flat_hash_map<std::tuple<string_view, const Scope*>, const DPIExportSyntax*> exportsByScope;
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

        string_view cId = getCId(*scope, syntax->c_identifier, syntax->name);
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

void Compilation::checkExternIfaceMethods(span<const MethodPrototypeSymbol* const> protos) {
    for (auto proto : protos) {
        if (!proto->getFirstExternImpl() && !proto->flags.has(MethodFlags::ForkJoin)) {
            auto scope = proto->getParentScope();
            ASSERT(scope);

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
    span<const std::pair<const InterfacePortSymbol*, const ModportSymbol*>> modports) {

    for (auto [port, modport] : modports) {
        auto def = port->getDeclaringDefinition();
        ASSERT(def);

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

void Compilation::resolveDefParams(size_t) {
    TimeTraceScope timeScope("resolveDefParams"sv, ""sv);

    struct OverrideEntry {
        std::string path;
        const SyntaxNode* node = nullptr;
        ConstantValue value;
    };
    SmallVector<OverrideEntry, 4> overrides;

    auto copyOverrides = [&](Compilation& c) {
        for (auto& entry : overrides) {
            ParamOverrideNode* node = &c.paramOverrides;
            std::string curr = entry.path;
            while (true) {
                size_t idx = curr.find('.');
                if (idx == curr.npos) {
                    node->overrides[curr] = entry.value;
                    break;
                }

                node = &node->childNodes[curr.substr(0, idx)];
                curr = curr.substr(idx + 1);
            }
        }
    };

    auto createClone = [&](Compilation& c) {
        c.options = options;
        for (auto& tree : syntaxTrees)
            c.addSyntaxTree(tree);

        copyOverrides(c);
    };

    auto saveDefparams = [&](DefParamVisitor& visitor) {
        overrides.clear();
        for (auto defparam : visitor.found) {
            auto target = defparam->getTarget();
            if (!target)
                overrides.emplace_back();
            else {
                std::string path;
                target->getHierarchicalPath(path);
                overrides.push_back({std::move(path), target->getSyntax(), defparam->getValue()});
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
    while (true) {
        // Traverse the design and find all defparams and their values.
        // defparam resolution happens in a cloned compilation unit because we will be
        // constantly mucking with parameter values in ways that can change the actual
        // hierarchy that gets instantiated. Cloning lets us do that in an isolated context
        // and throw that work away once we know the final parameter values.
        Compilation initialClone;
        createClone(initialClone);

        DefParamVisitor initialVisitor(options.maxInstanceDepth, generateLevel);
        initialClone.getRoot(/* skipDefParamResolution */ true).visit(initialVisitor);
        saveDefparams(initialVisitor);
        if (checkProblem(initialVisitor))
            return;

        // defparams can change the value of parameters, further affecting the value of
        // other defparams elsewhere in the design. This means we need to iterate,
        // reevaluating defparams until they all settle to a stable value or until we
        // give up due to the potential of cyclical references.
        bool allSame = true;
        for (uint32_t i = 0; i < options.maxDefParamSteps; i++) {
            Compilation c;
            createClone(c);

            DefParamVisitor v(options.maxInstanceDepth, generateLevel);
            c.getRoot(/* skipDefParamResolution */ true).visit(v);
            if (checkProblem(v))
                return;

            // We're only done if we have the same set of defparams with the same set of values.
            allSame = true;
            ASSERT(v.found.size() == overrides.size());
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
                    ASSERT(syntax);
                    return syntax->sourceRange();
                };

                auto& prevEntry = overrides[j];
                if (prevEntry.node && targetNode && prevEntry.node != targetNode) {
                    std::string path;
                    target->getHierarchicalPath(path);

                    auto& diag = root->addDiag(diag::DefParamTargetChange, getRange());
                    diag << prevEntry.path;
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

            saveDefparams(v);
        }

        // If we gave up due to a potential infinite loop, continue exiting.
        if (!allSame)
            break;

        ASSERT(initialVisitor.numBlocksSeen >= numBlocksSeen);
        if (initialVisitor.numBlocksSeen == numBlocksSeen)
            break;

        generateLevel++;
        numBlocksSeen = initialVisitor.numBlocksSeen;
    }

    // We have our final overrides; copy them into the main compilation unit.
    copyOverrides(*this);
}

} // namespace slang::ast
