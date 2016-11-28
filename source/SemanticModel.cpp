//------------------------------------------------------------------------------
// SemanticModel.cpp
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "SemanticModel.h"

#include "Scope.h"
#include "SyntaxTree.h"

namespace {

using namespace slang;

TokenKind getIntegralKeywordKind(bool isFourState, bool isReg) {
    return !isFourState ? TokenKind::BitKeyword : isReg ? TokenKind::RegKeyword : TokenKind::LogicKeyword;
}

}

namespace slang {

SemanticModel::SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable) :
    alloc(alloc), diagnostics(diagnostics), binder(*this), declTable(declTable)
{
    knownTypes[SyntaxKind::ShortIntType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::ShortIntKeyword, 16, true, false);
    knownTypes[SyntaxKind::IntType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntKeyword, 32, true, false);
    knownTypes[SyntaxKind::LongIntType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::LongIntKeyword, 64, true, false);
    knownTypes[SyntaxKind::ByteType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::ByteKeyword, 8, true, false);
    knownTypes[SyntaxKind::BitType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::BitKeyword, 1, false, false);
    knownTypes[SyntaxKind::LogicType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::LogicKeyword, 1, false, true);
    knownTypes[SyntaxKind::RegType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::RegKeyword, 1, false, true);
    knownTypes[SyntaxKind::IntegerType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::IntegerKeyword, 32, true, true);
    knownTypes[SyntaxKind::TimeType] = alloc.emplace<IntegralTypeSymbol>(TokenKind::TimeKeyword, 64, false, true);
    knownTypes[SyntaxKind::RealType] = alloc.emplace<RealTypeSymbol>(TokenKind::RealKeyword, 64);
    knownTypes[SyntaxKind::RealTimeType] = alloc.emplace<RealTypeSymbol>(TokenKind::RealTimeKeyword, 64);
    knownTypes[SyntaxKind::ShortRealType] = alloc.emplace<RealTypeSymbol>(TokenKind::ShortRealKeyword, 32);
    knownTypes[SyntaxKind::StringType] = alloc.emplace<TypeSymbol>(SymbolKind::StringType, "string", SourceLocation());
    knownTypes[SyntaxKind::CHandleType] = alloc.emplace<TypeSymbol>(SymbolKind::CHandleType, "chandle", SourceLocation());
    knownTypes[SyntaxKind::VoidType] = alloc.emplace<TypeSymbol>(SymbolKind::VoidType, "void", SourceLocation());
    knownTypes[SyntaxKind::EventType] = alloc.emplace<TypeSymbol>(SymbolKind::EventType, "event", SourceLocation());
    knownTypes[SyntaxKind::Unknown] = alloc.emplace<ErrorTypeSymbol>();
}

InstanceSymbol* SemanticModel::makeImplicitInstance(const ModuleDeclarationSyntax* syntax) {
    return makeInstance(syntax, nullptr);
}

InstanceSymbol* SemanticModel::makeInstance(const ModuleDeclarationSyntax* decl, const ParameterValueAssignmentSyntax* parameterAssignments) {
    ASSERT(decl);

    // TODO: check that this can actually be implicit (i.e. no parameters without initializers)

    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    bool hasParamAssignments = false;
    bool orderedAssignments = false;
    SmallVectorSized<OrderedArgumentSyntax*, 8> orderedParams;
    SmallHashMap<StringRef, NamedArgumentSyntax*, 8> namedParams;

    if (parameterAssignments) {
        for (auto paramBase : parameterAssignments->parameters->parameters) {
            bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
            if (!hasParamAssignments) {
                hasParamAssignments = true;
                orderedAssignments = isOrdered;
            }
            else if (isOrdered != orderedAssignments) {
                diagnostics.add(DiagCode::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
                break;
            }

            if (isOrdered)
                orderedParams.append(paramBase->as<OrderedArgumentSyntax>());
            else {
                NamedArgumentSyntax* nas = paramBase->as<NamedArgumentSyntax>();
                if (!namedParams.add(nas->name.valueText(), nas)) {

                }
            }
        }
    }
    
    // Discover all of the element's parameters. If we have a parameter port list, the only
    // publicly visible parameters are the ones in that list. Otherwise, parameters declared
    // in the module body are publicly visible.
    const ModuleHeaderSyntax* header = decl->header;
    SmallVectorSized<ParameterSymbol*, 8> portParameters;
    SmallHashMap<StringRef, SourceLocation, 16> nameDupMap;

    bool overrideLocal = false;
    if (header->parameters) {
        bool lastLocal = false;
        for (const ParameterDeclarationSyntax* paramDecl : header->parameters->declarations)
            lastLocal = makeParameters(paramDecl, portParameters, nameDupMap, lastLocal, false, false);
        overrideLocal = true;
    }

    // also find direct body parameters
    SmallVectorSized<ParameterSymbol*, 8> bodyParameters;
    for (const MemberSyntax* member : decl->members) {
        if (member->kind == SyntaxKind::ParameterDeclarationStatement)
            makeParameters(member->as<ParameterDeclarationStatementSyntax>()->parameter, bodyParameters,
                           nameDupMap, false, overrideLocal, true);
    }

    // Now evaluate initializers and finalize the type of each parameter.
    // Do ports separately from body parameters.
    auto portScope = pushScope(portParameters);
    for (ParameterSymbol* param : portParameters)
        evaluateParameter(param);

    auto bodyScope = pushScope(bodyParameters);
    for (ParameterSymbol* param : bodyParameters)
        evaluateParameter(param);

    // Handle all child instantiations.
    for (const MemberSyntax* member : decl->members) {
        if (member->kind == SyntaxKind::HierarchyInstantiation) {
            // Look up the module declaration for this instance. If we don't find it just
            // silently continue; an error has already been issued for it.
            auto his = member->as<HierarchyInstantiationSyntax>();
            const ModuleDeclarationSyntax* module = declTable.find(his->type.valueText());
            if (!module)
                makeInstance(module, his->parameters);
        }
    }

    return alloc.emplace<InstanceSymbol>(portParameters.copy(alloc), bodyParameters.copy(alloc));
}

const TypeSymbol* SemanticModel::makeTypeSymbol(const DataTypeSyntax* syntax) {
    ASSERT(syntax);

    switch (syntax->kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType: {
            // simple integral vector (possibly of just one element)
            auto its = syntax->as<IntegerTypeSyntax>();
            bool isReg = its->keyword.kind == TokenKind::RegKeyword;
            bool isSigned = its->signing.kind == TokenKind::SignedKeyword;
            bool isFourState = syntax->kind != SyntaxKind::BitType;
            SmallVectorSized<ConstantRange, 4> dims;
            if (!evaluateConstantDims(its->dimensions, dims))
                return getErrorType();

            // TODO: bounds checking on sizes, no X allowed

            if (dims.empty())
                // TODO: signing
                return getKnownType(syntax->kind);
            else if (dims.count() == 1 && dims[0].lsb == 0) {
                // if we have the common case of only one dimension and lsb == 0
                // then we can use the shared representation
                uint16_t width = dims[0].msb.getAssertUInt16() + 1;
                return getIntegralType(width, isSigned, isFourState, isReg);
            }
            else {
                SmallVectorSized<int, 4> lowerBounds;
                SmallVectorSized<int, 4> widths;
                uint16_t totalWidth = 0;
                for (auto& dim : dims) {
                    // TODO: msb < lsb
                    uint16_t msb = dim.msb.getAssertUInt16();
                    uint16_t lsb = dim.lsb.getAssertUInt16();
                    uint16_t width = msb - lsb + 1;
                    lowerBounds.append(lsb);
                    widths.append(width);

                    // TODO: overflow
                    totalWidth += width;
                }
                return alloc.emplace<IntegralTypeSymbol>(
                    getIntegralKeywordKind(isFourState, isReg),
                    totalWidth, isSigned, isFourState,
                    lowerBounds.copy(alloc), widths.copy(alloc));
            }
        }
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            // TODO: signing
            auto its = syntax->as<IntegerTypeSyntax>();
            if (its->dimensions.count() > 0) {
                // Error but don't fail out; just remove the dims and keep trucking
                auto& diag = diagnostics.add(DiagCode::PackedDimsOnPredefinedType, its->dimensions[0]->openBracket.location());
                diag << getTokenKindText(its->keyword.kind);
            }
            return getKnownType(syntax->kind);
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
            return getKnownType(syntax->kind);
        case SyntaxKind::TypedefDeclaration: {
            auto tds = syntax->as<TypedefDeclarationSyntax>();
            auto type = makeTypeSymbol(tds->type);
            return alloc.emplace<TypeAliasSymbol>(syntax, tds->name.location(), type, tds->name.valueText());
        }
    }

    // TODO: consider Void Type

    return nullptr;
}

bool SemanticModel::evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results) {
    for (const VariableDimensionSyntax* dim : dimensions) {
        const SelectorSyntax* selector;
        if (!dim->specifier || dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier ||
            (selector = dim->specifier->as<RangeDimensionSpecifierSyntax>()->selector)->kind != SyntaxKind::SimpleRangeSelect) {

            auto& diag = diagnostics.add(DiagCode::PackedDimRequiresConstantRange, dim->specifier->getFirstToken().location());
            diag << dim->specifier->sourceRange();
            return false;
        }

        const RangeSelectSyntax* range = selector->as<RangeSelectSyntax>();
        auto msbExpr = binder.bindConstantExpression(range->left);
        auto lsbExpr = binder.bindConstantExpression(range->right);
        if (msbExpr->bad || lsbExpr->bad)
            return false;

        // TODO: ensure integer here
        results.emplace(ConstantRange {std::get<SVInt>(msbExpr->constantValue), std::get<SVInt>(lsbExpr->constantValue)});
    }
    return true;
}

bool SemanticModel::makeParameters(const ParameterDeclarationSyntax* syntax, SmallVector<ParameterSymbol*>& buffer,
                                   HashMapBase<StringRef, SourceLocation>& nameDupMap,
                                   bool lastLocal, bool overrideLocal, bool bodyParam)
{
    // It's legal to leave off the parameter keyword in the parameter port list.
    // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
    // This isn't allowed in a module body, but the parser will take care of the error for us.
    bool local = false;
    auto p = syntax->as<ParameterDeclarationSyntax>();
    if (!p->keyword)
        local = lastLocal;
    else {
        // In the body of a module that has a parameter port list in its header, parameters are
        // actually just localparams. overrideLocal will be true in this case.
        local = p->keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
    }

    for (const VariableDeclaratorSyntax* declarator : p->declarators) {
        auto name = declarator->name.valueText();
        if (!name)
            continue;

        auto location = declarator->name.location();
        if (!nameDupMap.add(name, location)) {
            diagnostics.add(DiagCode::DuplicateParameter, location) << name;
            diagnostics.add(DiagCode::NotePreviousDefinition, nameDupMap[name]);
        }
        else {
            ExpressionSyntax* init = nullptr;
            if (declarator->initializer)
                init = declarator->initializer->expr;
            else if (local)
                diagnostics.add(DiagCode::LocalParamNoInitializer, location);
            else if (bodyParam)
                diagnostics.add(DiagCode::BodyParamNoInitializer, location);
            buffer.append(alloc.emplace<ParameterSymbol>(name, location, p, init, local));
        }
    }
    return local;
}

void SemanticModel::evaluateParameter(ParameterSymbol* parameter) {
    // If no type is given, infer the type from the initializer
    DataTypeSyntax* typeSyntax = parameter->syntax->type;
    if (!typeSyntax) {
        BoundExpression* expr = binder.bindSelfDeterminedExpression(parameter->initializer);
        parameter->type = expr->type;
        parameter->value = expr->constantValue;
    }
    else {
        parameter->type = makeTypeSymbol(typeSyntax);
        BoundExpression* expr = binder.bindAssignmentLikeContext(parameter->initializer, parameter->location, parameter->type);
        parameter->value = expr->constantValue;
    }
}

const TypeSymbol* SemanticModel::getKnownType(SyntaxKind kind) const {
    auto it = knownTypes.find(kind);
    if (it == knownTypes.end())
        return getErrorType();
    return it->second;
}

const TypeSymbol* SemanticModel::getIntegralType(int width, bool isSigned, bool isFourState, bool isReg) {
    uint64_t key = width;
    key |= uint64_t(isSigned) << 32;
    key |= uint64_t(isFourState) << 33;
    key |= uint64_t(isReg) << 34;

    auto it = integralTypeCache.find(key);
    if (it != integralTypeCache.end())
        return it->second;

    TokenKind type = getIntegralKeywordKind(isFourState, isReg);
    auto symbol = alloc.emplace<IntegralTypeSymbol>(type, width, isSigned, isFourState);
    integralTypeCache.emplace_hint(it, key, symbol);
    return symbol;
}

SemanticModel::ScopePtr SemanticModel::pushScope() {
    scopeStack.emplace_back();
    return ScopePtr(&scopeStack.back(), [this](Scope* s) { popScope(s); });
}

template<typename TContainer>
SemanticModel::ScopePtr SemanticModel::pushScope(const TContainer& range) {
    auto scope = pushScope();
    scope->addRange(range);
    return scope;
}

void SemanticModel::popScope(const Scope* scope) {
    ASSERT(!scopeStack.empty());
    ASSERT(&scopeStack.back() == scope);
    scopeStack.pop_back();
}

const Symbol* SemanticModel::lookupSymbol(StringRef name) {
    // TODO: soooo many things here...
    for (auto it = scopeStack.rbegin(); it != scopeStack.rend(); ++it) {
        const Symbol* result = it->lookup(name);
        if (result)
            return result;
    }
    return nullptr;
}

}