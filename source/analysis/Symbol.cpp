//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "analysis/Binder.h"
#include "analysis/ConstantEvaluator.h"
#include "diagnostics/Diagnostics.h"
#include "parsing/SyntaxTree.h"

namespace {

using namespace slang;

TokenKind getIntegralKeywordKind(bool isFourState, bool isReg) {
    return !isFourState ? TokenKind::BitKeyword : isReg ? TokenKind::RegKeyword : TokenKind::LogicKeyword;
}

bool containsName(const std::vector<std::unordered_set<string_view>>& scopeStack, string_view name) {
    for (const auto& set : scopeStack) {
        if (set.find(name) != set.end())
            return true;
    }
    return false;
}

}

namespace slang {

VariableLifetime getLifetimeFromToken(Token token, VariableLifetime defaultIfUnset) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        default: return defaultIfUnset;
    }
}

SymbolList createSymbols(const SyntaxNode& node, const ScopeSymbol& parent) {
    const DesignRootSymbol& root = parent.getRoot();
    SmallVectorSized<const Symbol*, 4> results;

    switch (node.kind) {
        case SyntaxKind::ModuleDeclaration:
            results.append(&root.allocate<ModuleSymbol>(node.as<ModuleDeclarationSyntax>(), parent));
            break;
        case SyntaxKind::InterfaceDeclaration:
            // TODO:
            break;
        case SyntaxKind::PackageDeclaration:
            results.append(&root.allocate<PackageSymbol>(node.as<ModuleDeclarationSyntax>(), parent));
            break;
        case SyntaxKind::PackageImportDeclaration:
            for (auto item : node.as<PackageImportDeclarationSyntax>().items) {
                if (item->item.kind == TokenKind::Star) {
                    results.append(&root.allocate<WildcardImportSymbol>(
                        item->package.valueText(),
                        item->item.location(),
                        parent));
                }
                else {
                    results.append(&root.allocate<ExplicitImportSymbol>(
                        item->package.valueText(),
                        item->item.valueText(),
                        item->item.location(),
                        parent));
                }
            }
            break;
        case SyntaxKind::HierarchyInstantiation: {
            const auto& his = node.as<HierarchyInstantiationSyntax>();
            // TODO: module namespacing
            auto symbol = parent.lookup(his.type.valueText(), his.type.location(), LookupKind::Definition);
            if (symbol) {
                const auto& pms = symbol->as<ModuleSymbol>().parameterize(his.parameters, &parent);
                for (auto instance : his.instances) {
                    // TODO: handle arrays
                    results.append(&root.allocate<ModuleInstanceSymbol>(instance->name.valueText(),
                                                                        instance->name.location(),
                                                                        pms, parent));
                }
            }
            break;
        }
        case SyntaxKind::IfGenerate: {
            // TODO: add special name conflict checks for generate blocks
            SmallVectorSized<const GenerateBlockSymbol*, 2> blocks;
            GenerateBlockSymbol::fromSyntax(parent, node.as<IfGenerateSyntax>(), blocks);

            for (auto block : blocks)
                results.append(block);
            break;
        }
        case SyntaxKind::LoopGenerate: {
            SmallVectorSized<const GenerateBlockSymbol*, 4> blocks;
            GenerateBlockSymbol::fromSyntax(parent, node.as<LoopGenerateSyntax>(), blocks);

            for (auto block : blocks)
                results.append(block);
            break;
        }
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            results.append(&root.allocate<SubroutineSymbol>(node.as<FunctionDeclarationSyntax>(), parent));
            break;
        case SyntaxKind::DataDeclaration: {
            SmallVectorSized<const VariableSymbol*, 4> variables;
            VariableSymbol::fromSyntax(parent, node.as<DataDeclarationSyntax>(), variables);

            for (auto variable : variables)
                results.append(variable);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            const ParameterDeclarationSyntax& declaration = node.as<ParameterDeclarationStatementSyntax>().parameter;
            for (const VariableDeclaratorSyntax* decl : declaration.declarators) {

                // TODO: hack to get param values working
                //auto it = paramAssignments.find(decl->name.valueText());
                const ConstantValue& cv = parent.evaluateConstant(decl->initializer->expr);

                results.append(&root.allocate<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                    root.getKnownType(SyntaxKind::IntType), cv, parent));
            }
            break;
        }
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysLatchBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock:
            results.append(&root.allocate<ProceduralBlockSymbol>(node.as<ProceduralBlockSyntax>(), parent));
            break;
        DEFAULT_UNREACHABLE;
    }

    return results.copy(root.allocator());
}

const Symbol* Symbol::findAncestor(SymbolKind searchKind) const {
    const Symbol* current = this;
    while (current->kind != searchKind) {
        if (current->kind == SymbolKind::Root)
            return nullptr;

        current = &current->containingSymbol;
    }
    return current;
}

const ScopeSymbol& Symbol::containingScope() const {
    const Symbol* current = this;
    while (true) {
        current = &current->containingSymbol;
        switch (current->kind) {
            case SymbolKind::Root:
            case SymbolKind::CompilationUnit:
            case SymbolKind::Package:
            case SymbolKind::ParameterizedModule:
            case SymbolKind::SequentialBlock:
            case SymbolKind::ProceduralBlock:
            case SymbolKind::GenerateBlock:
            case SymbolKind::DynamicScope:
            case SymbolKind::Subroutine:
                return *static_cast<const ScopeSymbol*>(current);

            default: break;
        }
    }
}

const DesignRootSymbol& Symbol::getRoot() const {
    const Symbol* symbol = findAncestor(SymbolKind::Root);
    ASSERT(symbol);
    return symbol->as<DesignRootSymbol>();
}

Diagnostic& Symbol::addError(DiagCode code, SourceLocation location_) const {
    return getRoot().addError(code, location_);
}

const Symbol* ScopeSymbol::lookup(string_view searchName, SourceLocation lookupLocation,
                                  LookupKind lookupKind) const {
    init();

    // If the parser added a missing identifier token, it already issued an
    // appropriate error. This check here makes it easier to silently continue
    // in that case without checking every time someone wants to do a lookup.
    if (searchName.empty())
        return nullptr;

    // First, do a direct search within the current scope's name map.
    const SourceManager& sm = getRoot().sourceManager();
    auto it = memberMap.find(searchName);
    if (it != memberMap.end()) {
        // If this is a local or scoped lookup, check that we can access
        // the symbol (it must be declared before usage). Callables can be
        // referenced anywhere in the scope; location doesn't matter.
        bool locationGood = true;
        const Symbol* result = it->second;
        if (lookupKind == LookupKind::Local || lookupKind == LookupKind::Scoped)
            locationGood = sm.isBeforeInCompilationUnit(result->location, lookupLocation);

        if (locationGood) {
            // If this is a package import, unwrap it to return the imported symbol.
            // Direct lookups don't allow package imports, so ignore it in that case.
            if (result->kind == SymbolKind::ExplicitImport || result->kind == SymbolKind::ImplicitImport) {
                if (lookupKind != LookupKind::Direct)
                    return result->as<ExplicitImportSymbol>().importedSymbol();
            }
            else {
                return result;
            }
        }
    }

    // If we got here, we didn't find a viable symbol locally. Depending on the lookup
    // kind, try searching elsewhere.
    if (lookupKind == LookupKind::Direct)
        return nullptr;

    if (kind == SymbolKind::Root) {
        // For scoped lookups, if we reach the root without finding anything,
        // look for a package.
        if (lookupKind == LookupKind::Scoped)
            return getRoot().findPackage(searchName);
        return nullptr;
    }

    if (lookupKind != LookupKind::Definition) {
        // Check wildcard imports that lexically preceed the lookup location
        // to see if the symbol can be found in one of them.
        for (auto wildcard : wildcardImports) {
            if (sm.isBeforeInCompilationUnit(wildcard->location, lookupLocation)) {
                // TODO: if we find multiple, error and report all matching locations
                auto result = wildcard->resolve(searchName, lookupLocation);
                if (result) {
                    // TODO: this can cause other errors for this particular scope
                    addMember(*result);
                    return result->importedSymbol();
                }
            }
        }
    }

    // Continue up the scope chain.
    return containingScope().lookup(searchName, lookupLocation, lookupKind);
}

SymbolList ScopeSymbol::members() const {
    init();
    return memberList;
}

ConstantValue ScopeSymbol::evaluateConstant(const ExpressionSyntax& expr) const {
    const auto& bound = Binder(*this).bindConstantExpression(expr);
    if (bound.bad())
        return nullptr;
    return ConstantEvaluator().evaluateExpr(bound);
}

ConstantValue ScopeSymbol::evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType, SourceLocation errorLocation) const {
    const auto& bound = Binder(*this).bindAssignmentLikeContext(expr, errorLocation ? errorLocation : expr.getFirstToken().location(), targetType);
    if (bound.bad())
        return nullptr;
    return ConstantEvaluator().evaluateExpr(bound);
}

const TypeSymbol& ScopeSymbol::getType(const DataTypeSyntax& syntax) const {
    return getRoot().getType(syntax, *this);
}

void ScopeSymbol::addMember(const Symbol& symbol) const {
    // TODO: check for duplicate names
    // TODO: packages and definition namespaces
    memberList.push_back(&symbol);
    if (!symbol.name.empty())
        memberMap.try_emplace(symbol.name, &symbol);

    if (symbol.kind == SymbolKind::WildcardImport)
        wildcardImports.push_back(&symbol.as<WildcardImportSymbol>());
}

void ScopeSymbol::init() const {
    if (!membersInitialized) {
        membersInitialized = true;
        initMembers();
    }
}

DynamicScopeSymbol::DynamicScopeSymbol(const Symbol& parent) : ScopeSymbol(SymbolKind::DynamicScope, parent) {}

void DynamicScopeSymbol::addSymbol(const Symbol& symbol) {
    ScopeSymbol::addMember(symbol);
}

SymbolList DynamicScopeSymbol::createAndAddSymbols(const SyntaxNode& node) {
    SymbolList symbols = createSymbols(node, *this);
    for (auto symbol : symbols)
        addMember(*symbol);
    return symbols;
}

DesignRootSymbol::DesignRootSymbol(const SourceManager& sourceManager) :
    ScopeSymbol(SymbolKind::Root, *this),
    sourceMan(sourceManager)
{
    // Register built-in types
    knownTypes[SyntaxKind::ShortIntType]  = alloc.emplace<IntegralTypeSymbol>(TokenKind::ShortIntKeyword,   16, true, false, *this);
    knownTypes[SyntaxKind::IntType]       = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntKeyword,        32, true, false, *this);
    knownTypes[SyntaxKind::LongIntType]   = alloc.emplace<IntegralTypeSymbol>(TokenKind::LongIntKeyword,    64, true, false, *this);
    knownTypes[SyntaxKind::ByteType]      = alloc.emplace<IntegralTypeSymbol>(TokenKind::ByteKeyword,       8, true, false, *this);
    knownTypes[SyntaxKind::BitType]       = alloc.emplace<IntegralTypeSymbol>(TokenKind::BitKeyword,        1, false, false, *this);
    knownTypes[SyntaxKind::LogicType]     = alloc.emplace<IntegralTypeSymbol>(TokenKind::LogicKeyword,      1, false, true, *this);
    knownTypes[SyntaxKind::RegType]       = alloc.emplace<IntegralTypeSymbol>(TokenKind::RegKeyword,        1, false, true, *this);
    knownTypes[SyntaxKind::IntegerType]   = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntegerKeyword,    32, true, true, *this);
    knownTypes[SyntaxKind::TimeType]      = alloc.emplace<IntegralTypeSymbol>(TokenKind::TimeKeyword,       64, false, true, *this);
    knownTypes[SyntaxKind::RealType]      = alloc.emplace<RealTypeSymbol>(TokenKind::RealKeyword,       64, *this);
    knownTypes[SyntaxKind::RealTimeType]  = alloc.emplace<RealTypeSymbol>(TokenKind::RealTimeKeyword,   64, *this);
    knownTypes[SyntaxKind::ShortRealType] = alloc.emplace<RealTypeSymbol>(TokenKind::ShortRealKeyword,  32, *this);
    knownTypes[SyntaxKind::StringType]    = alloc.emplace<TypeSymbol>(SymbolKind::StringType,   "string", *this);
    knownTypes[SyntaxKind::CHandleType]   = alloc.emplace<TypeSymbol>(SymbolKind::CHandleType,  "chandle", *this);
    knownTypes[SyntaxKind::VoidType]      = alloc.emplace<TypeSymbol>(SymbolKind::VoidType,     "void", *this);
    knownTypes[SyntaxKind::EventType]     = alloc.emplace<TypeSymbol>(SymbolKind::EventType,    "event", *this);
    knownTypes[SyntaxKind::Unknown]       = alloc.emplace<ErrorTypeSymbol>(*this);

    // Register built-in system functions
    const auto& intType = getKnownType(SyntaxKind::IntType);
    SmallVectorSized<const FormalArgumentSymbol*, 8> args;

    args.append(alloc.emplace<FormalArgumentSymbol>(intType, *this));
    addMember(allocate<SubroutineSymbol>("$clog2", intType, args.copy(alloc), SystemFunction::clog2, *this));

    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    const auto& trivialIntType = getIntegralType(1, false, true);
    args.clear();
    args.append(alloc.emplace<FormalArgumentSymbol>(trivialIntType, *this));
    addMember(allocate<SubroutineSymbol>("$bits", intType, args.copy(alloc), SystemFunction::bits, *this));
    addMember(allocate<SubroutineSymbol>("$left", intType, args.copy(alloc), SystemFunction::left, *this));
    addMember(allocate<SubroutineSymbol>("$right", intType, args.copy(alloc), SystemFunction::right, *this));
    addMember(allocate<SubroutineSymbol>("$low", intType, args.copy(alloc), SystemFunction::low, *this));
    addMember(allocate<SubroutineSymbol>("$high", intType, args.copy(alloc), SystemFunction::high, *this));
    addMember(allocate<SubroutineSymbol>("$size", intType, args.copy(alloc), SystemFunction::size, *this));
    addMember(allocate<SubroutineSymbol>("$increment", intType, args.copy(alloc), SystemFunction::increment, *this));
}

DesignRootSymbol::DesignRootSymbol(const SourceManager& sourceManager, span<const CompilationUnitSyntax* const> units) :
    DesignRootSymbol(sourceManager)
{
    for (auto unit : units)
        addCompilationUnit(allocate<CompilationUnitSymbol>(*unit, *this));
}

DesignRootSymbol::DesignRootSymbol(const SyntaxTree* tree) :
    DesignRootSymbol(make_span(&tree, 1)) {}

DesignRootSymbol::DesignRootSymbol(span<const SyntaxTree* const> trees) :
    DesignRootSymbol(trees[0]->sourceManager())
{
    for (auto tree : trees) {
        ASSERT(&tree->sourceManager() == &sourceMan);

        if (tree->root().kind == SyntaxKind::CompilationUnit)
            addCompilationUnit(allocate<CompilationUnitSymbol>(tree->root().as<CompilationUnitSyntax>(), *this));
        else {
            SymbolList symbols = createSymbols(tree->root(), *this);
            // TODO: fix parent pointer to be the compilation unit
            addCompilationUnit(allocate<CompilationUnitSymbol>(symbols, *this));
        }
    }
}

const PackageSymbol* DesignRootSymbol::findPackage(string_view lookupName) const {
    init();

    auto it = packageMap.find(lookupName);
    if (it == packageMap.end())
        return nullptr;

    return (const PackageSymbol*)it->second;
}

const TypeSymbol& DesignRootSymbol::getType(const DataTypeSyntax& syntax) const {
    return getType(syntax, *this);
}

const TypeSymbol& DesignRootSymbol::getType(const DataTypeSyntax& syntax, const ScopeSymbol& scope) const {
    switch (syntax.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return getIntegralType(syntax.as<IntegerTypeSyntax>(), scope);
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            // TODO: signing
            auto& its = syntax.as<IntegerTypeSyntax>();
            if (its.dimensions.count() > 0) {
                // Error but don't fail out; just remove the dims and keep trucking
                auto& diag = addError(DiagCode::PackedDimsOnPredefinedType, its.dimensions[0]->openBracket.location());
                diag << getTokenKindText(its.keyword.kind);
            }
            return getKnownType(syntax.kind);
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
            return getKnownType(syntax.kind);
        //case SyntaxKind::EnumType: {
        //    ExpressionBinder binder {*this, scope};
        //    const EnumTypeSyntax& enumSyntax = syntax.as<EnumTypeSyntax>();
        //    const IntegralTypeSymbol& baseType = (enumSyntax.baseType ? getTypeSymbol(*enumSyntax.baseType, scope) : getKnownType(SyntaxKind::IntType))->as<IntegralTypeSymbol>();

        //    SmallVectorSized<EnumValueSymbol *, 8> values;
        //    SVInt nextVal;
        //    for (auto member : enumSyntax.members) {
        //        //TODO: add each member to the scope
        //        if (member->initializer) {
        //            auto bound = binder.bindConstantExpression(member->initializer->expr);
        //            nextVal = std::get<SVInt>(evaluateConstant(bound));
        //        }
        //        EnumValueSymbol *valSymbol = alloc.emplace<EnumValueSymbol>(member->name.valueText(), member->name.location(), &baseType, nextVal);
        //        values.append(valSymbol);
        //        scope->add(valSymbol);
        //        ++nextVal;
        //    }
        //    return alloc.emplace<EnumTypeSymbol>(&baseType, enumSyntax.keyword.location(), values.copy(alloc));
        //}
        //case SyntaxKind::TypedefDeclaration: {
        //    const auto& tds = syntax.as<TypedefDeclarationSyntax>();
        //    auto type = getTypeSymbol(tds.type, scope);
        //    return alloc.emplace<TypeAliasSymbol>(syntax, tds.name.location(), type, tds.name.valueText());
        //}
        default:
            break;
    }

    // TODO: consider Void Type

    return getErrorType();
}

const TypeSymbol& DesignRootSymbol::getKnownType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    ASSERT(it != knownTypes.end());
    return *it->second;
}

const TypeSymbol& DesignRootSymbol::getIntegralType(int width, bool isSigned, bool isFourState, bool isReg) const {
    uint64_t key = width;
    key |= uint64_t(isSigned) << 32;
    key |= uint64_t(isFourState) << 33;
    key |= uint64_t(isReg) << 34;

    auto it = integralTypeCache.find(key);
    if (it != integralTypeCache.end())
        return *it->second;

    TokenKind type = getIntegralKeywordKind(isFourState, isReg);
    auto symbol = alloc.emplace<IntegralTypeSymbol>(type, width, isSigned, isFourState, *this);
    integralTypeCache.emplace_hint(it, key, symbol);
    return *symbol;
}

const TypeSymbol& DesignRootSymbol::getIntegralType(const IntegerTypeSyntax& syntax, const ScopeSymbol& scope) const {
    // This is a simple integral vector (possibly of just one element).
    bool isReg = syntax.keyword.kind == TokenKind::RegKeyword;
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = syntax.kind != SyntaxKind::BitType;

    SmallVectorSized<ConstantRange, 4> dims;
    if (!evaluateConstantDims(syntax.dimensions, dims, scope))
        return getErrorType();

    // TODO: review this whole mess

    if (dims.empty())
        // TODO: signing
        return getKnownType(syntax.kind);
    else if (dims.size() == 1 && dims[0].right == 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        int width = dims[0].left + 1;
        return getIntegralType(width, isSigned, isFourState, isReg);
    }
    else {
        SmallVectorSized<int, 4> lowerBounds;
        SmallVectorSized<int, 4> widths;
        int totalWidth = 0;
        for (auto& dim : dims) {
            int msb = dim.left;
            int lsb = dim.right;
            int width;
            if (msb > lsb) {
                width = msb - lsb + 1;
                lowerBounds.append(lsb);
            }
            else {
                // TODO: msb == lsb
                width = lsb - msb + 1;
                lowerBounds.append(-lsb);
            }
            widths.append(width);

            // TODO: overflow
            totalWidth += width;
        }
        return allocate<IntegralTypeSymbol>(
            getIntegralKeywordKind(isFourState, isReg),
            totalWidth, isSigned, isFourState,
            lowerBounds.copy(alloc), widths.copy(alloc), *this);
    }
}

const TypeSymbol& DesignRootSymbol::getErrorType() const {
    return getKnownType(SyntaxKind::Unknown);
}

bool DesignRootSymbol::evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const ScopeSymbol& scope) const {
    for (const VariableDimensionSyntax* dim : dimensions) {
        const SelectorSyntax* selector;
        if (!dim->specifier || dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier ||
            (selector = &dim->specifier->as<RangeDimensionSpecifierSyntax>().selector)->kind != SyntaxKind::SimpleRangeSelect) {

            auto& diag = addError(DiagCode::PackedDimRequiresConstantRange, dim->specifier->getFirstToken().location());
            diag << dim->specifier->sourceRange();
            return false;
        }

        const RangeSelectSyntax& range = selector->as<RangeSelectSyntax>();

        // §6.9.1 - Implementations may set a limit on the maximum length of a vector, but the limit shall be at least 65536 (2^16) bits.
        const int MaxRangeBits = 16;

        // TODO: errors
        auto left = scope.evaluateConstant(range.left).coerceInteger(MaxRangeBits);
        auto right = scope.evaluateConstant(range.right).coerceInteger(MaxRangeBits);

        if (!left || !right)
            return false;

        results.emplace(ConstantRange { *left, *right });
    }
    return true;
}

void DesignRootSymbol::addCompilationUnit(const CompilationUnitSymbol& unit) {
    unitList.push_back(&unit);

    // Add all modules to the root scope; we can look up modules anywhere in the design.
    // Also keep track of packages separately; they live in their own namespace.
    for (auto symbol : unit.members()) {
        switch (symbol->kind) {
            case SymbolKind::Module:
                addMember(*symbol);
                break;
            case SymbolKind::Package:
                packageMap.emplace(symbol->name, symbol);
                break;
            default:
                break;
        }
    }
}

void DesignRootSymbol::initMembers() const {
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
                std::vector<NameSet> scopeStack;
                findInstantiations(member->as<ModuleSymbol>().syntax, scopeStack, instances);
            }
        }
    }

    // Now loop back over and find modules that have no instantiations.
    for (auto symbol : unitList) {
        for (auto member : symbol->members()) {
            if (member->kind == SymbolKind::Module && instances.count(member->name) == 0) {
                // TODO: check for no parameters here
                const auto& pms = member->as<ModuleSymbol>().parameterize();
                const auto& instance = allocate<ModuleInstanceSymbol>(member->name, SourceLocation(), pms, *this);
                addMember(instance);
                topList.push_back(&instance);
            }
        }
    }
}

void DesignRootSymbol::findInstantiations(const ModuleDeclarationSyntax& module, std::vector<NameSet>& scopeStack,
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

void DesignRootSymbol::findInstantiations(const MemberSyntax& node, std::vector<NameSet>& scopeStack,
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
