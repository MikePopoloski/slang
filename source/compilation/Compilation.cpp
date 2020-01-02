//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"

#include <nlohmann/json.hpp>

#include "slang/binding/SystemSubroutine.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

namespace {

using namespace slang;

// This visitor is used to make sure we've found all module instantiations in the design.
struct ElaborationVisitor : public ASTVisitor<ElaborationVisitor> {
    template<typename T>
    void handle(const T&) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }
    void handle(const CompilationUnitSymbol& symbol) { visitDefault(symbol); }
    void handle(const DefinitionSymbol& symbol) { visitDefault(symbol); }
    void handle(const ModuleInstanceSymbol& symbol) { visitDefault(symbol); }
    void handle(const InstanceArraySymbol& symbol) { visitDefault(symbol); }
    void handle(const GenerateBlockSymbol& symbol) { visitDefault(symbol); }
    void handle(const GenerateBlockArraySymbol& symbol) { visitDefault(symbol); }
};

// This visitor is used to touch every node in the AST to ensure that all lazily
// evaluated members have been realized and we have recorded every diagnostic.
struct DiagnosticVisitor : public ASTVisitor<DiagnosticVisitor> {
    DiagnosticVisitor(Compilation& compilation, const Diagnostics& diags, uint32_t errorLimit) :
        compilation(compilation), diags(diags), errorLimit(errorLimit) {}

    template<typename T>
    void handle(const T& symbol) {
        if (diags.getNumErrors() > errorLimit)
            return;

        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto declaredType = symbol.getDeclaredType();
            if (declaredType) {
                declaredType->getType();
                declaredType->getInitializer();
            }

            for (auto attr : compilation.getAttributes(symbol))
                attr->getValue();
        }

        visitDefault(symbol);
    }
    void handle(const ExplicitImportSymbol& symbol) { symbol.importedSymbol(); }
    void handle(const WildcardImportSymbol& symbol) { symbol.getPackage(); }
    void handle(const ContinuousAssignSymbol& symbol) { symbol.getAssignment(); }

    void handle(const DefinitionSymbol& symbol) {
        if (diags.getNumErrors() > errorLimit)
            return;

        auto guard = ScopeGuard([saved = inDef, this] { inDef = saved; });
        inDef = true;
        visitDefault(symbol);
    }

    void handleInstance(const InstanceSymbol& symbol) {
        if (diags.getNumErrors() > errorLimit)
            return;

        if (!inDef)
            instanceCount[&symbol.definition]++;
        visitDefault(symbol);
    }

    void handle(const ModuleInstanceSymbol& symbol) { handleInstance(symbol); }
    void handle(const ProgramInstanceSymbol& symbol) { handleInstance(symbol); }
    void handle(const InterfaceInstanceSymbol& symbol) { handleInstance(symbol); }

    void handle(const PortSymbol& symbol) {
        for (auto attr : symbol.getConnectionAttributes())
            attr->getValue();
    }

    void handle(const InterfacePortSymbol& symbol) {
        for (auto attr : symbol.connectionAttributes)
            attr->getValue();
    }

    Compilation& compilation;
    const Diagnostics& diags;
    flat_hash_map<const Symbol*, size_t> instanceCount;
    uint32_t errorLimit;
    bool inDef = false;
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

} // namespace slang::Builtins

namespace slang {

Compilation::Compilation(const Bag& options) : options(options.getOrDefault<CompilationOptions>()) {
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

    for (auto& [node, meta] : tree->getMetadataMap()) {
        auto decl = &node->as<ModuleDeclarationSyntax>();
        defaultNetTypeMap.emplace(decl, &getNetType(meta.defaultNetType));

        if (meta.timeScale)
            timeScaleDirectiveMap.emplace(decl, *meta.timeScale);
    }

    auto unit = emplace<CompilationUnitSymbol>(*this);
    const SyntaxNode& node = tree->root();
    if (node.kind == SyntaxKind::CompilationUnit) {
        for (auto member : node.as<CompilationUnitSyntax>().members)
            unit->addMembers(*member);
    }
    else {
        unit->addMembers(node);
    }

    const SyntaxNode* topNode = &node;
    while (topNode->parent)
        topNode = topNode->parent;

    unit->setSyntax(*topNode);
    root->addMember(*unit);
    compilationUnits.push_back(unit);
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

    ASSERT(!finalizing);
    finalizing = true;
    auto guard = ScopeGuard([this] { finalizing = false; });

    // Visit all compilation units added to the design.
    ElaborationVisitor elaborationVisitor;
    root->visit(elaborationVisitor);

    // Find modules that have no instantiations. Iterate the definitions map
    // before instantiating any top level modules, since that can cause changes
    // to the definition map itself.
    SmallVectorSized<const DefinitionSymbol*, 8> topDefinitions;
    for (auto& [key, defTuple] : definitionMap) {
        // Ignore definitions that are not top level. Top level definitions are:
        // - Always modules
        // - Not nested
        // - Have no non-defaulted parameters
        // - Not instantiated anywhere
        auto [definition, everInstantiated] = defTuple;
        if (everInstantiated || std::get<1>(key) != root.get() ||
            definition->definitionKind != DefinitionKind::Module) {
            continue;
        }

        bool allDefaulted = true;
        for (auto param : definition->parameters) {
            if (!param->hasDefault()) {
                allDefaulted = false;
                break;
            }
        }
        if (!allDefaulted)
            continue;

        topDefinitions.append(definition);
    }

    // Sort the list of definitions so that we get deterministic ordering of instances;
    // the order is otherwise dependent on iterating over a hash table.
    std::sort(topDefinitions.begin(), topDefinitions.end(),
              [](auto a, auto b) { return a->name < b->name; });

    SmallVectorSized<const ModuleInstanceSymbol*, 4> topList;
    for (auto def : topDefinitions) {
        auto& instance = ModuleInstanceSymbol::instantiate(*this, def->name, def->location, *def);
        root->addMember(instance);
        topList.append(&instance);
    }

    root->topInstances = topList.copy(*this);
    root->compilationUnits = compilationUnits;
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

const DefinitionSymbol* Compilation::getDefinition(string_view lookupName,
                                                   const Scope& scope) const {
    const Scope* searchScope = &scope;
    while (searchScope) {
        auto it = definitionMap.find(std::make_tuple(lookupName, searchScope));
        if (it != definitionMap.end()) {
            std::get<1>(it->second) = true;
            return std::get<0>(it->second);
        }

        auto& sym = searchScope->asSymbol();
        if (sym.kind == SymbolKind::Root)
            return nullptr;

        searchScope = sym.getLexicalScope();
    }

    return nullptr;
}

const DefinitionSymbol* Compilation::getDefinition(string_view lookupName) const {
    return getDefinition(lookupName, *root);
}

void Compilation::addDefinition(const DefinitionSymbol& definition) {
    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    const Scope* scope = definition.getParentScope();
    ASSERT(scope);

    if (scope->asSymbol().kind == SymbolKind::CompilationUnit) {
        definitionMap.emplace(std::make_tuple(definition.name, root.get()),
                              std::make_tuple(&definition, false));
    }
    else {
        definitionMap.emplace(std::make_tuple(definition.name, scope),
                              std::make_tuple(&definition, false));
    }
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

const NameSyntax& Compilation::parseName(string_view name) {
    Diagnostics localDiags;
    SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
    Preprocessor preprocessor(sourceMan, *this, localDiags);
    preprocessor.pushSource(sourceMan.assignText(name));

    Parser parser(preprocessor);
    auto& result = parser.parseName();

    if (!localDiags.empty()) {
        localDiags.sort(sourceMan);
        throw std::runtime_error(DiagnosticEngine::reportAll(sourceMan, localDiags));
    }

    return result;
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
    DiagnosticVisitor visitor(*this, diags,
                              options.errorLimit == 0 ? UINT32_MAX : options.errorLimit);
    getRoot().visit(visitor);

    // Go through all diagnostics and build a map from source location / code to the
    // actual diagnostic. The purpose is to find duplicate diagnostics issued by several
    // instantiations and collapse them down to one output for the user.
    flat_hash_map<std::tuple<DiagCode, SourceLocation>,
                  std::pair<const Diagnostic*, std::vector<const Diagnostic*>>>
        diagMap;

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

    auto getInstanceOrDef = [](const Symbol* symbol) {
        while (symbol && symbol->kind != SymbolKind::Definition &&
               !InstanceSymbol::isKind(symbol->kind)) {
            auto scope = symbol->getParentScope();
            symbol = scope ? &scope->asSymbol() : nullptr;
        }
        return symbol;
    };

    auto isInsideDef = [](const Symbol* symbol) {
        while (true) {
            if (symbol->kind == SymbolKind::Definition)
                return true;

            auto scope = symbol->getParentScope();
            if (!scope)
                return false;

            symbol = &scope->asSymbol();
        }
    };

    for (auto& diag : diags) {
        // Filter out diagnostics that came from inside an uninstantiated generate block.
        ASSERT(diag.symbol);
        if (isSuppressed(diag.symbol))
            continue;

        auto inst = getInstanceOrDef(diag.symbol);

        // Coalesce diagnostics that are at the same source location and have the same code.
        if (auto it = diagMap.find({ diag.code, diag.location }); it != diagMap.end()) {
            it->second.second.push_back(&diag);
            if (inst && inst->kind == SymbolKind::Definition)
                it->second.first = &diag;
        }
        else {
            std::pair<const Diagnostic*, std::vector<const Diagnostic*>> newEntry;
            newEntry.second.push_back(&diag);
            if (inst && inst->kind == SymbolKind::Definition)
                newEntry.first = &diag;

            diagMap.emplace(std::make_tuple(diag.code, diag.location), std::move(newEntry));
        }
    }

    Diagnostics results;
    for (auto& pair : diagMap) {
        // Figure out which diagnostic from this group to issue.
        // If any of them are inside a definition (as opposed to one or more instances), issue
        // the one for the definition without embellishment. Otherwise, pick the first instance
        // and include a note about where the diagnostic occurred in the hierarchy.
        auto& [definition, diagList] = pair.second;
        if (definition) {
            results.append(*definition);
            continue;
        }

        // Try to find a diagnostic in an instance that isn't at the top-level
        // (printing such a path seems silly).
        const Diagnostic* found = nullptr;
        const Symbol* inst = nullptr;
        size_t count = 0;

        for (auto d : diagList) {
            auto symbol = getInstanceOrDef(d->symbol);
            if (!symbol || !symbol->getParentScope())
                continue;

            // Don't count the diagnostic if it's inside a definition instead of an instance.
            if (isInsideDef(symbol))
                continue;

            count++;
            auto& parent = symbol->getParentScope()->asSymbol();
            if (parent.kind != SymbolKind::Root && parent.kind != SymbolKind::CompilationUnit) {
                found = d;
                inst = symbol;
            }
        }

        // If the diagnostic is present in all instances, don't bother
        // providing specific instantiation info.
        if (found && visitor.instanceCount[&inst->as<InstanceSymbol>().definition] > count) {
            Diagnostic diag = *found;
            diag.symbol = getInstanceOrDef(inst);
            diag.coalesceCount = count;
            results.append(std::move(diag));
        }
        else {
            results.append(*diagList.front());
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
    diags.appendRange(diagnostics);
}

const NetType& Compilation::getDefaultNetType(const ModuleDeclarationSyntax& decl) const {
    auto it = defaultNetTypeMap.find(&decl);
    if (it == defaultNetTypeMap.end())
        return getNetType(TokenKind::Unknown);
    return *it->second;
}

optional<TimeScale> Compilation::getDirectiveTimeScale(const ModuleDeclarationSyntax& decl) const {
    auto it = timeScaleDirectiveMap.find(&decl);
    if (it == timeScaleDirectiveMap.end())
        return std::nullopt;
    return it->second;
}

const Type& Compilation::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? *errorType : *it->second;
}

const Type& Compilation::getType(const DataTypeSyntax& node, LookupLocation location,
                                 const Scope& parent, bool forceSigned) {
    return Type::fromSyntax(*this, node, location, parent, forceSigned);
}

const Type& Compilation::getType(const Type& elementType,
                                 const SyntaxList<VariableDimensionSyntax>& dimensions,
                                 LookupLocation location, const Scope& scope) {
    return UnpackedArrayType::fromSyntax(*this, elementType, location, scope, dimensions);
}

const Type& Compilation::getType(bitwidth_t width, bitmask<IntegralFlags> flags) {
    ASSERT(width > 0);
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

namespace {
using NameSet = flat_hash_set<string_view>;
}

static void findInstantiations(const MemberSyntax& node, SmallVector<NameSet>& scopeStack,
                               NameSet& found);

static void findInstantiations(const ModuleDeclarationSyntax& module,
                               SmallVector<NameSet>& scopeStack, NameSet& found) {
    // If there are nested modules that shadow global module names, we need to
    // ignore them when considering instantiations.
    NameSet* localDefs = nullptr;
    for (auto member : module.members) {
        switch (member->kind) {
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ProgramDeclaration: {
                // ignore empty names
                string_view name = member->as<ModuleDeclarationSyntax>().header->name.valueText();
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

static bool containsName(const SmallVector<flat_hash_set<string_view>>& scopeStack,
                         string_view name) {
    for (const auto& set : scopeStack) {
        if (set.find(name) != set.end())
            return true;
    }
    return false;
}

static void findInstantiations(const MemberSyntax& node, SmallVector<NameSet>& scopeStack,
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
            findInstantiations(*node.as<LoopGenerateSyntax>().block, scopeStack, found);
            break;
        case SyntaxKind::CaseGenerate:
            for (auto& item : node.as<CaseGenerateSyntax>().items) {
                switch (item->kind) {
                    case SyntaxKind::DefaultCaseItem:
                        findInstantiations(
                            item->as<DefaultCaseItemSyntax>().clause->as<MemberSyntax>(),
                            scopeStack, found);
                        break;
                    case SyntaxKind::StandardCaseItem:
                        findInstantiations(
                            item->as<StandardCaseItemSyntax>().clause->as<MemberSyntax>(),
                            scopeStack, found);
                        break;
                    default:
                        break;
                }
            }
            break;
        case SyntaxKind::IfGenerate: {
            const auto& ifGen = node.as<IfGenerateSyntax>();
            findInstantiations(*ifGen.block, scopeStack, found);
            if (ifGen.elseClause)
                findInstantiations(ifGen.elseClause->clause->as<MemberSyntax>(), scopeStack, found);
            break;
        }
        default:
            break;
    }
}

void Compilation::noteUninstantiatedGenerateBlock(const SyntaxNode& node) {
    if (!visitedGenBlocks.insert(&node).second)
        return;

    NameSet instances;
    SmallVectorSized<NameSet, 2> scopeStack;
    findInstantiations(node.as<MemberSyntax>(), scopeStack, instances);

    for (string_view entry : instances)
        getDefinition(entry);
}

} // namespace slang
