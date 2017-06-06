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

bool containsName(const std::vector<std::unordered_set<StringRef>>& scopeStack, StringRef name) {
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
        //DEFAULT_UNREACHABLE;
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
            /*case SymbolKind::CompilationUnit:
            case SymbolKind::Package:
            case SymbolKind::ParameterizedModule:*/
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

const Symbol* ScopeSymbol::lookup(StringRef searchName, LookupNamespace ns) const {
    init();

    // TODO:
    auto it = memberMap.find(searchName);
    if (it != memberMap.end())
        return it->second;

    if (kind == SymbolKind::Root)
        return nullptr;

    return containingScope().lookup(searchName, ns);
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
    memberMap.try_emplace(symbol.name, &symbol);
    memberList.push_back(&symbol);
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

DesignRootSymbol::DesignRootSymbol() :
	ScopeSymbol(SymbolKind::Root, *this)
{
	// Register built-in types
	knownTypes[SyntaxKind::ShortIntType]  = alloc.emplace<IntegralTypeSymbol>(TokenKind::ShortIntKeyword,	16, true, false, *this);
	knownTypes[SyntaxKind::IntType]		  = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntKeyword,		32, true, false, *this);
	knownTypes[SyntaxKind::LongIntType]	  = alloc.emplace<IntegralTypeSymbol>(TokenKind::LongIntKeyword,	64, true, false, *this);
	knownTypes[SyntaxKind::ByteType]	  = alloc.emplace<IntegralTypeSymbol>(TokenKind::ByteKeyword,		8, true, false, *this);
	knownTypes[SyntaxKind::BitType]		  = alloc.emplace<IntegralTypeSymbol>(TokenKind::BitKeyword,		1, false, false, *this);
	knownTypes[SyntaxKind::LogicType]	  = alloc.emplace<IntegralTypeSymbol>(TokenKind::LogicKeyword,		1, false, true, *this);
	knownTypes[SyntaxKind::RegType]		  = alloc.emplace<IntegralTypeSymbol>(TokenKind::RegKeyword,		1, false, true, *this);
	knownTypes[SyntaxKind::IntegerType]	  = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntegerKeyword,	32, true, true, *this);
	knownTypes[SyntaxKind::TimeType]	  = alloc.emplace<IntegralTypeSymbol>(TokenKind::TimeKeyword,		64, false, true, *this);
	knownTypes[SyntaxKind::RealType]	  = alloc.emplace<RealTypeSymbol>(TokenKind::RealKeyword,		64, *this);
	knownTypes[SyntaxKind::RealTimeType]  = alloc.emplace<RealTypeSymbol>(TokenKind::RealTimeKeyword,	64, *this);
	knownTypes[SyntaxKind::ShortRealType] = alloc.emplace<RealTypeSymbol>(TokenKind::ShortRealKeyword,	32, *this);
	knownTypes[SyntaxKind::StringType]	  = alloc.emplace<TypeSymbol>(SymbolKind::StringType,	"string", *this);
	knownTypes[SyntaxKind::CHandleType]	  = alloc.emplace<TypeSymbol>(SymbolKind::CHandleType,	"chandle", *this);
	knownTypes[SyntaxKind::VoidType]	  = alloc.emplace<TypeSymbol>(SymbolKind::VoidType,		"void", *this);
	knownTypes[SyntaxKind::EventType]	  = alloc.emplace<TypeSymbol>(SymbolKind::EventType,	"event", *this);
    knownTypes[SyntaxKind::Unknown]       = alloc.emplace<ErrorTypeSymbol>(*this);

    // Register built-in system functions
    auto intType = getKnownType(SyntaxKind::IntType);
    SmallVectorSized<const FormalArgumentSymbol*, 8> args;
    
    args.append(alloc.emplace<FormalArgumentSymbol>(intType, *this));
    addMember(allocate<SubroutineSymbol>("$clog2", intType, args.copy(alloc), SystemFunction::clog2, *this));
    
    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    auto trivialIntType = getIntegralType(1, false, true);
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

DesignRootSymbol::DesignRootSymbol(ArrayRef<const CompilationUnitSyntax*> units) :
    DesignRootSymbol()
{
    for (auto unit : units)
        addCompilationUnit(allocate<CompilationUnitSymbol>(*unit, *this));
}

DesignRootSymbol::DesignRootSymbol(const SyntaxTree& tree) :
    DesignRootSymbol(ArrayRef<const SyntaxTree*> { &tree }) {}

DesignRootSymbol::DesignRootSymbol(ArrayRef<const SyntaxTree*> trees) :
    DesignRootSymbol()
{
    for (auto tree : trees) {
        if (tree->root().kind == SyntaxKind::CompilationUnit)
            addCompilationUnit(allocate<CompilationUnitSymbol>(tree->root().as<CompilationUnitSyntax>(), *this));
        else {
            SymbolList symbols = createSymbols(tree->root(), *this);
            addCompilationUnit(allocate<CompilationUnitSymbol>(symbols, *this));
        }
    }
}

const PackageSymbol* DesignRootSymbol::findPackage(StringRef lookupName) const {
	// TODO
	return nullptr;
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
	else if (dims.count() == 1 && dims[0].right == 0) {
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

		bool bad = false;
        results.emplace(ConstantRange {
            coerceInteger(scope.evaluateConstant(range.left), MaxRangeBits, bad),
            coerceInteger(scope.evaluateConstant(range.right), MaxRangeBits, bad)
        });

		if (bad)
			return false;
    }
    return true;
}

int DesignRootSymbol::coerceInteger(const ConstantValue& cv, uint32_t maxRangeBits, bool& bad) const {
	// TODO: report errors
	if (cv.isInteger()) {
		const SVInt& value = cv.integer();
		if (!value.hasUnknown() && value.getActiveBits() <= maxRangeBits) {
			auto result = value.asBuiltIn<int>();
			if (result)
				return *result;
		}
	}

	bad = true;
	return 0;
}

void DesignRootSymbol::addCompilationUnit(const CompilationUnitSymbol& unit) {
    unitList.push_back(&unit);

    // Add all modules to the root scope; we can look up modules anywhere in the design
    for (auto symbol : unit.members()) {
        if (symbol->kind == SymbolKind::Module)
            addMember(*symbol);
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
                const auto& instance = allocate<ModuleInstanceSymbol>(pms, *this);
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
                auto name = member->as<ModuleDeclarationSyntax>().header.name.valueText();
                if (name) {
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
            auto name = his.type.valueText();
            if (name && !containsName(scopeStack, name))
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
