//------------------------------------------------------------------------------
// SemanticModel.cpp
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "SemanticModel.h"

#include "ConstantEvaluator.h"
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
    alloc(alloc), diagnostics(diagnostics), declTable(declTable)
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
    SmallVectorSized<const ParameterSymbol*, 8> parameters;
    makePublicParameters(parameters, syntax, nullptr, Scope::Empty, SourceLocation(), true);

    const ModuleSymbol* module = makeModule(syntax, parameters.copy(alloc));
    return alloc.emplace<InstanceSymbol>(module, true);
}

const ModuleSymbol* SemanticModel::makeModule(const ModuleDeclarationSyntax* syntax, ArrayRef<const ParameterSymbol*> parameters) {
    Scope* scope = alloc.emplace<Scope>();
    scope->addRange(parameters);

    SmallVectorSized<const Symbol*, 8> children;
    for (const MemberSyntax* member : syntax->members) {
        switch (member->kind) {
            case SyntaxKind::HierarchyInstantiation:
                handleInstantiation(member->as<HierarchyInstantiationSyntax>(), children);
                break;
            case SyntaxKind::LoopGenerate:
                break;
            case SyntaxKind::IfGenerate:
                // TODO: scope
                handleIfGenerate(member->as<IfGenerateSyntax>(), children, scope);
                break;
            case SyntaxKind::CaseGenerate:
                break;
        }
    }

    // TODO: cache this shit
    return alloc.emplace<ModuleSymbol>(syntax, scope, children.copy(alloc));
}

const TypeSymbol* SemanticModel::makeTypeSymbol(const DataTypeSyntax* syntax, const Scope* scope) {
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
            if (!evaluateConstantDims(its->dimensions, dims, scope))
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
            auto type = makeTypeSymbol(tds->type, scope);
            return alloc.emplace<TypeAliasSymbol>(syntax, tds->name.location(), type, tds->name.valueText());
        }
    }

    // TODO: consider Void Type

    return nullptr;
}

bool SemanticModel::evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const Scope* scope) {
    ExpressionBinder binder { *this, scope };
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
        if (msbExpr->bad() || lsbExpr->bad())
            return false;

        // TODO: ensure integer here
        results.emplace(ConstantRange {
            std::get<SVInt>(evaluateConstant(msbExpr)),
            std::get<SVInt>(evaluateConstant(lsbExpr))
        });
    }
    return true;
}

const std::vector<SemanticModel::ParameterInfo>& SemanticModel::getModuleParams(const ModuleDeclarationSyntax* syntax) {
    auto it = parameterCache.find(syntax);
    if (it == parameterCache.end()) {
        // Discover all of the element's parameters. If we have a parameter port list, the only
        // publicly visible parameters are the ones in that list. Otherwise, parameters declared
        // in the module body are publicly visible.
        const ModuleHeaderSyntax* header = syntax->header;
        SmallHashMap<StringRef, SourceLocation, 16> nameDupMap;
        std::vector<ParameterInfo> buffer;

        bool overrideLocal = false;
        if (header->parameters) {
            bool lastLocal = false;
            for (const ParameterDeclarationSyntax* paramDecl : header->parameters->declarations)
                lastLocal = getParamDecls(paramDecl, buffer, nameDupMap, lastLocal, false, false);
            overrideLocal = true;
        }

        // also find direct body parameters
        for (const MemberSyntax* member : syntax->members) {
            if (member->kind == SyntaxKind::ParameterDeclarationStatement)
                getParamDecls(member->as<ParameterDeclarationStatementSyntax>()->parameter, buffer,
                    nameDupMap, false, overrideLocal, true);
        }

        it = parameterCache.emplace(syntax, std::move(buffer)).first;
    }
    return it->second;
}

bool SemanticModel::getParamDecls(const ParameterDeclarationSyntax* syntax, std::vector<ParameterInfo>& buffer,
                                  HashMapBase<StringRef, SourceLocation>& nameDupMap,
                                  bool lastLocal, bool overrideLocal, bool bodyParam)
{
    // It's legal to leave off the parameter keyword in the parameter port list.
    // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
    // This isn't allowed in a module body, but the parser will take care of the error for us.
    bool local = false;
    if (!syntax->keyword)
        local = lastLocal;
    else {
        // In the body of a module that has a parameter port list in its header, parameters are
        // actually just localparams. overrideLocal will be true in this case.
        local = syntax->keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
    }

    for (const VariableDeclaratorSyntax* declarator : syntax->declarators) {
        auto name = declarator->name.valueText();
        if (!name)
            continue;

        auto location = declarator->name.location();
        auto pair = nameDupMap.emplace(name, location);
        if (!pair.second) {
            diagnostics.add(DiagCode::DuplicateDefinition, location) << StringRef("parameter") << name;
            diagnostics.add(DiagCode::NotePreviousDefinition, pair.first->second);
        }
        else {
            ExpressionSyntax* init = nullptr;
            if (declarator->initializer)
                init = declarator->initializer->expr;
            else if (local)
                diagnostics.add(DiagCode::LocalParamNoInitializer, location);
            else if (bodyParam)
                diagnostics.add(DiagCode::BodyParamNoInitializer, location);
            buffer.push_back({ syntax, name, location, init, local, bodyParam });
        }
    }
    return local;
}

void SemanticModel::evaluateParameter(ParameterSymbol* symbol, const ExpressionSyntax* initializer, const Scope* scope) {
    // If no type is given, infer the type from the initializer
    ExpressionBinder binder { *this, scope };
    DataTypeSyntax* typeSyntax = symbol->syntax->type;
    if (!typeSyntax) {
        BoundExpression* expr = binder.bindSelfDeterminedExpression(initializer);
        symbol->type = expr->type;
        symbol->value = evaluateConstant(expr);
    }
    else {
        const TypeSymbol* type = makeTypeSymbol(typeSyntax, scope);
        BoundExpression* expr = binder.bindAssignmentLikeContext(initializer, symbol->location, type);
        symbol->type = type;
        symbol->value = evaluateConstant(expr);
    }
}

void SemanticModel::handleInstantiation(const HierarchyInstantiationSyntax* syntax, SmallVector<const Symbol*>& results) {
    // Try to find the module/interface/program being instantiated; we can't do anything without it.
    // We've already reported an error for missing modules.
    const ModuleDeclarationSyntax* decl = declTable.find(syntax->type.valueText());
    if (!decl)
        return;

    // Evaluate public parameter assignments
    SmallVectorSized<const ParameterSymbol*, 8> parameterBuilder;
    makePublicParameters(parameterBuilder, decl, syntax->parameters, Scope::Empty, syntax->getFirstToken().location(), false);

    ArrayRef<const ParameterSymbol*> parameters = parameterBuilder.copy(alloc);
    for (const HierarchicalInstanceSyntax* instance : syntax->instances) {
        // Get a symbol for this particular parameterized form of the module
        const ModuleSymbol* module = makeModule(decl, parameters);
        results.append(alloc.emplace<InstanceSymbol>(module, false));
    }
}

void SemanticModel::handleIfGenerate(const IfGenerateSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope) {
    // Evaluate the condition to decide if we should take the branch.
    ExpressionBinder binder { *this, scope };
    auto expr = binder.bindConstantExpression(syntax->condition);
    if (expr->bad())
        return;

    // TODO: don't assume the expression type here
    const SVInt& value = std::get<SVInt>(evaluateConstant(expr));
    if ((logic_t)value)
        handleGenerateBlock(syntax->block, results, scope);
    else if (syntax->elseClause)
        handleGenerateBlock(syntax->elseClause->clause->as<MemberSyntax>(), results, scope);
}

void SemanticModel::handleGenerateBlock(const MemberSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope) {
    if (syntax->kind == SyntaxKind::GenerateBlock) {
        SmallVectorSized<const Symbol*, 8> children;
        for (const MemberSyntax* member : syntax->as<GenerateBlockSyntax>()->members) {
            switch (member->kind) {
                case SyntaxKind::HierarchyInstantiation:
                    handleInstantiation(member->as<HierarchyInstantiationSyntax>(), children);
                    break;
            }
        }
        results.append(alloc.emplace<GenerateBlock>(children.copy(alloc)));
    }
    else {
        // TODO: handle simple member
    }
}

void SemanticModel::makePublicParameters(SmallVector<const ParameterSymbol*>& results, const ModuleDeclarationSyntax* decl,
                                         const ParameterValueAssignmentSyntax* parameterAssignments,
                                         const Scope* instantiationScope, SourceLocation instanceLocation, bool isTopLevel) {
    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<OrderedArgumentSyntax*, 8> orderedParams;
    SmallHashMap<StringRef, std::pair<NamedArgumentSyntax*, bool>, 8> namedParams;
    StringRef moduleName = decl->header->name.valueText();

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
                auto pair = namedParams.emplace(nas->name.valueText(), std::make_pair(nas, false));
                if (!pair.second) {
                    diagnostics.add(DiagCode::DuplicateParamAssignment, nas->name.location()) << nas->name.valueText();
                    diagnostics.add(DiagCode::NotePreviousUsage, pair.first->second.first->name.location());
                }
            }
        }
    }

    // Pre-create parameter symbol entries so that we can give better errors about use before decl.
    Scope declScope;
    const auto& moduleParamInfo = getModuleParams(decl);
    for (const auto& info : moduleParamInfo) {
        ParameterSymbol* symbol = alloc.emplace<ParameterSymbol>(info.name, info.location, info.paramDecl, info.local);
        results.append(symbol);
        declScope.add(symbol);
    }

    // Obtain the set of parameters actually declared in the module. This is a shared
    // representation. We'll turn this into actual parameter values using any provided
    // overrides. At this point any parameters without a default or an assigned value
    // get marked as an error.
    if (orderedAssignments) {
        // We take this branch if we had ordered parameter assignments,
        // or if we didn't have any parameter assignments at all.
        uint32_t orderedIndex = 0;
        int resultIndex = 0;
        bool moduleUnreferencedError = false;
        for (const auto& info : moduleParamInfo) {
            ExpressionSyntax* initializer;
            const Scope* scope;
            if (info.local || orderedIndex >= orderedParams.count()) {
                initializer = info.initializer;
                scope = &declScope;
            }
            else {
                initializer = orderedParams[orderedIndex++]->expr;
                scope = instantiationScope;
            }

            // If we have an initializer, evaluate it now. The const_cast is kosher, since we
            // just created the object up above. The reason it's const is that we are returning
            // the array to the caller and don't want him to modify it after this method finishes.
            if (initializer)
                evaluateParameter(const_cast<ParameterSymbol*>(results[resultIndex]), initializer, scope);
            else if (!info.local && !info.bodyParam) {
                // Otherwise error. Only report an error if this is a non-local non-body parameter;
                // we've already reported an error otherwise. The error we report differs slightly
                // depending on whether this is an implicit instantiation (top-level) or explicit.
                if (isTopLevel && !moduleUnreferencedError) {
                    auto& diag = diagnostics.add(DiagCode::ModuleUnreferenced, decl->header->name.location());
                    diag << moduleName;
                    moduleUnreferencedError = true;
                }
                else if (!isTopLevel) {
                    auto& diag = diagnostics.add(DiagCode::ParamHasNoValue, instanceLocation);
                    diag << moduleName;
                    diag << info.name;
                }
                diagnostics.add(DiagCode::NoteDeclarationHere, info.location) << StringRef("parameter");
            }
            resultIndex++;
        }

        // Make sure there aren't extra param assignments for non-existent params.
        if (orderedIndex < orderedParams.count()) {
            auto& diag = diagnostics.add(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
            diag << moduleName;
            diag << orderedParams.count();
            diag << orderedIndex;
        }
    }
    else {
        // Otherwise handle named assignments.
        int resultIndex = 0;
        for (const auto& info : moduleParamInfo) {
            ExpressionSyntax* initializer = nullptr;
            const Scope* scope = nullptr;
            auto it = namedParams.find(info.name);
            if (it != namedParams.end()) {
                NamedArgumentSyntax* arg = it->second.first;
                it->second.second = true;
                if (info.local) {
                    // Can't assign to localparams, so this is an error.
                    diagnostics.add(info.bodyParam ? DiagCode::AssignedToLocalBodyParam : DiagCode::AssignedToLocalPortParam, arg->name.location());
                    diagnostics.add(DiagCode::NoteDeclarationHere, info.location) << StringRef("parameter");
                }
                else {
                    initializer = arg->expr;
                    scope = instantiationScope;
                }
            }

            // If no initializer provided, use the default
            if (!initializer) {
                initializer = info.initializer;
                scope = &declScope;
            }

            // See above for note about const_cast.
            if (initializer)
                evaluateParameter(const_cast<ParameterSymbol*>(results[resultIndex]), initializer, scope);
            else if (!info.local && !info.bodyParam) {
                ASSERT(!isTopLevel);
                auto& diag = diagnostics.add(DiagCode::ParamHasNoValue, instanceLocation);
                diag << moduleName;
                diag << info.name;
                diagnostics.add(DiagCode::NoteDeclarationHere, info.location) << StringRef("parameter");
            }
            resultIndex++;
        }

        for (const auto& pair : namedParams) {
            // We nulled out any args that we used, so anything left over is a param assignment
            // for a non-existent parameter.
            if (!pair.second.second) {
                auto& diag = diagnostics.add(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                diag << pair.second.first->name.valueText();
                diag << moduleName;
            }
        }
    }
}

void SemanticModel::makeAttributes(SmallVector<const AttributeSymbol*>& results, const SyntaxList<AttributeInstanceSyntax>& attributes) {
    struct Entry {
        const AttributeSpecSyntax* attr;
        bool warned;
    };

    SmallHashMap<StringRef, Entry, 2> names;
    for (const AttributeInstanceSyntax* instance : attributes) {
        for (const AttributeSpecSyntax* attr : instance->specs) {
            StringRef name = attr->name.valueText();
            SourceLocation loc = attr->name.location();
            auto pair = names.emplace(name, Entry { attr, false });
            if (!pair.second) {
                // Duplicate name; spec says we should warn and take the last value we find.
                // The value in our hash is a pair, where the second element indicates whether
                // we've already warned about this name.
                Entry& entry = pair.first->second;
                if (!entry.warned) {
                    diagnostics.add(DiagCode::DuplicateAttribute, loc) << name;
                    diagnostics.add(DiagCode::NotePreviousDefinition, entry.attr->name.location());
                    entry.warned = true;
                }
                entry.attr = attr;
            }
        }
    }

    // Create the symbol entries
    for (const auto& pair : names) {
        const AttributeSpecSyntax* attr = pair.second.attr;
        const TypeSymbol* type;
        ConstantValue value;

        if (!attr->value) {
            // Default to a one bit value of 1
            type = getKnownType(SyntaxKind::BitType);
            value = SVInt(1, 1, false);
        }
        else {
            ExpressionBinder binder { *this, Scope::Empty };
            auto expr = binder.bindConstantExpression(attr->value->expr);
            type = expr->type;
            value = evaluateConstant(expr);
        }
        results.append(alloc.emplace<AttributeSymbol>(attr, type, value));
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

ConstantValue SemanticModel::evaluateConstant(const BoundNode* tree) {
    // TODO: eventually this will need diagnostics and other stuff
    ConstantEvaluator evaluator;
    return evaluator.evaluate(tree);
}

}
