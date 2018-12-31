//------------------------------------------------------------------------------
// Compilation.cpp
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"

#include "BuiltInSubroutines.h"

#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/SyntaxTree.h"

namespace {

using namespace slang;

// This visitor is used to make sure we've found all module instantiations in the design.
struct ElaborationVisitor : public ASTVisitor<ElaborationVisitor> {
    template<typename T>
    void handle(const T&) {}

    void handle(const RootSymbol& symbol) { visitDefault(symbol); }
    void handle(const CompilationUnitSymbol& symbol) { visitDefault(symbol); }
    void handle(const DefinitionSymbol& symbol) { visitDefault(symbol); }
    void handle(const InstanceSymbol& symbol) { visitDefault(symbol); }
    void handle(const InstanceArraySymbol& symbol) { visitDefault(symbol); }
    void handle(const GenerateBlockSymbol& symbol) { visitDefault(symbol); }
    void handle(const GenerateBlockArraySymbol& symbol) { visitDefault(symbol); }
};

// This visitor is used to touch every node in the AST to ensure that all lazily
// evaluated members have been realized and we have recorded every diagnostic.
struct DiagnosticVisitor : public ASTVisitor<DiagnosticVisitor> {
    template<typename T>
    void handle(const T& symbol) {
        if constexpr (std::is_base_of_v<Symbol, T>) {
            auto declaredType = symbol.getDeclaredType();
            if (declaredType) {
                declaredType->getType();
                declaredType->getInitializer();
            }
        }
        visitDefault(symbol);
    }
    void handle(const ExplicitImportSymbol& symbol) { symbol.importedSymbol(); }
    void handle(const WildcardImportSymbol& symbol) { symbol.getPackage(); }
    void handle(const ContinuousAssignSymbol& symbol) { symbol.getAssignment(); }
};

} // namespace

namespace slang {

Compilation::Compilation() :
    bitType(ScalarType::Bit), logicType(ScalarType::Logic), regType(ScalarType::Reg),
    signedBitType(ScalarType::Bit, true), signedLogicType(ScalarType::Logic, true),
    signedRegType(ScalarType::Reg, true), shortIntType(PredefinedIntegerType::ShortInt),
    intType(PredefinedIntegerType::Int), longIntType(PredefinedIntegerType::LongInt),
    byteType(PredefinedIntegerType::Byte), integerType(PredefinedIntegerType::Integer),
    timeType(PredefinedIntegerType::Time), realType(FloatingType::Real),
    realTimeType(FloatingType::RealTime), shortRealType(FloatingType::ShortReal) {

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
    knownTypes[SyntaxKind::NullLiteralExpression] = &nullType;
    knownTypes[SyntaxKind::EventType] = &eventType;
    knownTypes[SyntaxKind::Unknown] = &errorType;

    knownNetTypes[TokenKind::WireKeyword] = std::make_unique<NetType>(NetType::Wire);
    knownNetTypes[TokenKind::WAndKeyword] = std::make_unique<NetType>(NetType::WAnd);
    knownNetTypes[TokenKind::WOrKeyword] = std::make_unique<NetType>(NetType::WOr);
    knownNetTypes[TokenKind::TriKeyword] = std::make_unique<NetType>(NetType::Tri);
    knownNetTypes[TokenKind::TriAndKeyword] = std::make_unique<NetType>(NetType::TriAnd);
    knownNetTypes[TokenKind::TriOrKeyword] = std::make_unique<NetType>(NetType::TriOr);
    knownNetTypes[TokenKind::Tri0Keyword] = std::make_unique<NetType>(NetType::Tri0);
    knownNetTypes[TokenKind::Tri1Keyword] = std::make_unique<NetType>(NetType::Tri1);
    knownNetTypes[TokenKind::TriRegKeyword] = std::make_unique<NetType>(NetType::TriReg);
    knownNetTypes[TokenKind::Supply0Keyword] = std::make_unique<NetType>(NetType::Supply0);
    knownNetTypes[TokenKind::Supply1Keyword] = std::make_unique<NetType>(NetType::Supply1);
    knownNetTypes[TokenKind::UWireKeyword] = std::make_unique<NetType>(NetType::UWire);
    knownNetTypes[TokenKind::Unknown] = std::make_unique<NetType>(NetType::Unknown);
    wireNetType = knownNetTypes[TokenKind::WireKeyword].get();

    // Scalar types are indexed by bit flags.
    auto registerScalar = [this](auto& type) {
        scalarTypeTable[type.getIntegralFlags().bits() & 0x7] = &type;
    };
    registerScalar(bitType);
    registerScalar(logicType);
    registerScalar(regType);
    registerScalar(signedBitType);
    registerScalar(signedLogicType);
    registerScalar(signedRegType);

    root = std::make_unique<RootSymbol>(*this);

    // Register all system functions.
#define REGISTER(name) addSystemSubroutine(std::make_unique<Builtins::name##Subroutine>())
    REGISTER(Clog2);
    REGISTER(Bits);
    REGISTER(Low);
    REGISTER(High);
    REGISTER(Left);
    REGISTER(Right);
    REGISTER(Size);
    REGISTER(Increment);
#undef REGISTER

#define REGISTER(kind, name, ...) \
    addSystemMethod(kind, std::make_unique<Builtins::name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "first", true);
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "last", false);
    REGISTER(SymbolKind::EnumType, EnumNum, );
#undef REGISTER
}

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
    auto guard = finally([this] { finalizing = false; });

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
            if (!param->getDeclaredType()->getInitializerSyntax()) {
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

        instance.visit(elaborationVisitor);
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
    while (true) {
        auto it = definitionMap.find(std::make_tuple(lookupName, searchScope));
        if (it != definitionMap.end()) {
            std::get<1>(it->second) = true;
            return std::get<0>(it->second);
        }

        if (searchScope->asSymbol().kind == SymbolKind::Root)
            return nullptr;

        searchScope = searchScope->getParent();
    }
}

const DefinitionSymbol* Compilation::getDefinition(string_view lookupName) const {
    return getDefinition(lookupName, *root);
}

void Compilation::addDefinition(const DefinitionSymbol& definition) {
    // Record that the given scope contains this definition. If the scope is a compilation unit, add
    // it to the root scope instead so that lookups from other compilation units will find it.
    const Scope* scope = definition.getScope();
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

const NameSyntax& Compilation::parseName(string_view name) {
    SourceManager& sourceMan = SyntaxTree::getDefaultSourceManager();
    Preprocessor preprocessor(sourceMan, *this, diags);
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
    DiagnosticVisitor visitor;
    getRoot().visit(visitor);

    // Go through all diagnostics and build a map from source location / code to the
    // actual diagnostic. The purpose is to find duplicate diagnostics issued by several
    // instantiations and collapse them down to one output for the user.
    flat_hash_map<std::tuple<DiagCode, SourceLocation>,
                  std::pair<const Diagnostic*, std::vector<const Diagnostic*>>>
        diagMap;

    for (auto& diag : diags) {
        ASSERT(diag.symbol);
        if (diag.isSuppressed())
            continue;

        if (auto it = diagMap.find({ diag.code, diag.location }); it != diagMap.end()) {
            it->second.second.push_back(&diag);
            if (diag.symbol->kind == SymbolKind::Definition)
                it->second.first = &diag;
        }
        else {
            std::pair<const Diagnostic*, std::vector<const Diagnostic*>> newEntry;
            newEntry.second.push_back(&diag);
            if (diag.symbol->kind == SymbolKind::Definition)
                newEntry.first = &diag;

            diagMap.emplace(std::make_tuple(diag.code, diag.location), std::move(newEntry));
        }
    }

    Diagnostics results;
    for (auto& pair : diagMap) {
        auto& [definition, diagList] = pair.second;
        if (diagList.size() == 1)
            results.append(*diagList.front());
        else {
            // If we get here there are multiple duplicate diagnostics issued. Pick the one that
            // came from a Definition, if there is one. Otherwise just pick whatever the first one
            // is.
            // TODO: in the future this could print out the hierarchical paths or parameter values
            // involves with the instantiations to provide more insight as to what caused the error.
            if (definition)
                results.append(*definition);
            else
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

Diagnostic& Compilation::addDiag(const Symbol& source, DiagCode code, SourceLocation location) {
    return diags.add(source, code, location);
}

Diagnostic& Compilation::addDiag(const Symbol& source, DiagCode code, SourceRange sourceRange) {
    return diags.add(source, code, sourceRange);
}

void Compilation::addDiagnostics(const Diagnostics& diagnostics) {
    diags.appendRange(diagnostics);
}

const Type& Compilation::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? errorType : *it->second;
}

const Type& Compilation::getType(const DataTypeSyntax& node, LookupLocation location,
                                 const Scope& parent, bool allowNetType, bool forceSigned) {
    const Type& result = Type::fromSyntax(*this, node, location, parent, forceSigned);
    if (!allowNetType && result.isNetType()) {
        parent.addDiag(DiagCode::NetTypeNotAllowed, node.sourceRange()) << result.name;
        return errorType;
    }
    return result;
}

const Type& Compilation::getType(const Type& elementType,
                                 const SyntaxList<VariableDimensionSyntax>& dimensions,
                                 LookupLocation location, const Scope& scope) {
    return UnpackedArrayType::fromSyntax(*this, elementType, location, scope, dimensions);
}

const PackedArrayType& Compilation::getType(bitwidth_t width, bitmask<IntegralFlags> flags) {
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

const ScalarType& Compilation::getScalarType(bitmask<IntegralFlags> flags) {
    ScalarType* ptr = scalarTypeTable[flags.bits() & 0x7];
    ASSERT(ptr);
    return *ptr;
}

const NetType& Compilation::getNetType(TokenKind kind) const {
    auto it = knownNetTypes.find(kind);
    return it == knownNetTypes.end() ? *knownNetTypes.find(TokenKind::Unknown)->second
                                     : *it->second;
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

} // namespace slang
