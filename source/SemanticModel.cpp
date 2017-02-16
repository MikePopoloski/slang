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

VariableLifetime getLifetime(Token token, VariableLifetime defaultIfUnset) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        default: return defaultIfUnset;
    }
}

Diagnostics unusedDiagnostics;

}

namespace slang {

DeclarationTable SemanticModel::EmptyDeclTable { unusedDiagnostics };

SemanticModel::SemanticModel(SyntaxTree& tree) :
    SemanticModel(tree.allocator(), tree.diagnostics(), EmptyDeclTable)
{
}

SemanticModel::SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable) :
    alloc(alloc), diagnostics(diagnostics), declTable(declTable)
{
    // Register built-in types
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

    // Register built-in system functions
    auto intType = getKnownType(SyntaxKind::IntType);
    SmallVectorSized<const FormalArgumentSymbol*, 8> args;

    args.append(alloc.emplace<FormalArgumentSymbol>(intType));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$clog2", intType, args.copy(alloc), SystemFunction::clog2));

    // Assume input type has no width, so that the argument's self-determined type won't be expanded due to the
    // assignment like context
    // TODO: add support for all these operands on data_types, not just expressions,
    // and add support for things like unpacked arrays
    auto trivialIntType = getIntegralType(1, false, true);
    args.clear();
    args.append(alloc.emplace<FormalArgumentSymbol>(trivialIntType));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$bits", intType, args.copy(alloc), SystemFunction::bits));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$left", intType, args.copy(alloc), SystemFunction::left));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$right", intType, args.copy(alloc), SystemFunction::right));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$low", intType, args.copy(alloc), SystemFunction::low));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$high", intType, args.copy(alloc), SystemFunction::high));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$size", intType, args.copy(alloc), SystemFunction::size));
    systemScope.add(alloc.emplace<SubroutineSymbol>("$increment", intType, args.copy(alloc), SystemFunction::increment));
}

InstanceSymbol* SemanticModel::makeImplicitInstance(const ModuleDeclarationSyntax* syntax, Scope *definitions) {
    Scope* scope = alloc.emplace<Scope>();
    if (definitions) scope->addParentScope(definitions);
    makePublicParameters(scope, syntax, nullptr, definitions, SourceLocation(), true);
    const ModuleSymbol* module = makeModule(syntax, scope);
    return alloc.emplace<InstanceSymbol>(module, module->name, SourceLocation(), true);
}

void SemanticModel::makePackages() {
    for (auto pkg : declTable.getPackages()) {
        auto name = pkg->header->name.valueText();
        Scope *scope = alloc.emplace<Scope>();
        bool ok = packages.add(alloc.emplace<ModuleSymbol>(pkg, scope, ArrayRef<const Symbol *>()));
        ASSERT(ok);
    }
    for (auto pkg : declTable.getPackages()) {
        auto name = pkg->header->name.valueText();
        auto pkgSym = packages.lookup(name)->as<ModuleSymbol>();
        HashMap<StringRef, SourceLocation> nameDupMap;
        for (const MemberSyntax* member : pkg->members) {
            switch (member->kind) {
                case SyntaxKind::PackageImportDeclaration:
                    handlePackageImport(member->as<PackageImportDeclarationSyntax>(), pkgSym.scope);
                    break;
                case SyntaxKind::ParameterDeclarationStatement:
                    auto paramDecl = member->as<ParameterDeclarationStatementSyntax>()->parameter;
                    for (const VariableDeclaratorSyntax *declarator : paramDecl->declarators) {
                        auto declName = declarator->name.valueText();
                        ASSERT(declName);
                        auto location = declarator->name.location();
                        auto pair = nameDupMap.emplace(declName, location);
                        if (!pair.second) {
                            diagnostics.add(DiagCode::DuplicateDefinition, location)
                                << StringRef("parameter") << declName;
                            diagnostics.add(DiagCode::NotePreviousDefinition, pair.first->second);
                        } else if (!declarator->initializer) {
                            diagnostics.add(DiagCode::ParamHasNoValue, location)
                                << StringRef("parameter") << declName;
                        } else {
                            pkgSym.scope->add(alloc.emplace<ParameterSymbol>(declName, location, paramDecl, false));
                        }
                    }
                    break;
            }
        }
    }
    for (auto pkg : declTable.getPackages()) {
        auto name = pkg->header->name.valueText();
        auto pkgSym = packages.lookup(name)->as<ModuleSymbol>();
        for (auto sym : pkgSym.scope->symbols()) {
            if (sym->kind != SymbolKind::Parameter) continue;
            auto paramSym = sym->as<ParameterSymbol>();
            for (auto paramSyntax : paramSym.syntax->declarators)
                if (paramSyntax->name.valueText() == paramSym.name)
                    evaluateParameter(&paramSym, paramSyntax->initializer->expr, pkgSym.scope);
        }
    }
}

const ModuleSymbol* SemanticModel::makeModule(const ModuleDeclarationSyntax* syntax, Scope *scope) {
    SmallVectorSized<const Symbol*, 8> children;
    for (const MemberSyntax* member : syntax->members) {
        switch (member->kind) {
            case SyntaxKind::PackageImportDeclaration:
                handlePackageImport(member->as<PackageImportDeclarationSyntax>(), scope);
                break;
            case SyntaxKind::LoopGenerate:
                handleLoopGenerate(member->as<LoopGenerateSyntax>(), children, scope);
                break;
            case SyntaxKind::IfGenerate:
                // TODO: scope
                handleIfGenerate(member->as<IfGenerateSyntax>(), children, scope);
                break;
            case SyntaxKind::CaseGenerate:
                // TODO
                break;
            case SyntaxKind::GenvarDeclaration:
                handleGenvarDecl(member->as<GenvarDeclarationSyntax>(), children, scope);
                break;
            case SyntaxKind::HierarchyInstantiation:
            case SyntaxKind::InitialBlock:
            case SyntaxKind::FinalBlock:
            case SyntaxKind::AlwaysBlock:
            case SyntaxKind::AlwaysCombBlock:
            case SyntaxKind::AlwaysFFBlock:
            case SyntaxKind::AlwaysLatchBlock:
            case SyntaxKind::DataDeclaration:
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
                handleGenerateItem(member, children, scope);
                break;
            case SyntaxKind::ModuleDeclaration:
                // TODO: inner module
                break;
            case SyntaxKind::InterfaceDeclaration:
                // TODO: inner interface
                break;

            default:
                break;
        }
    }
    // TODO: cache pair<syntax,scope.toString()>
    return alloc.emplace<ModuleSymbol>(syntax, scope, children.copy(alloc));
}

const TypeSymbol* SemanticModel::makeTypeSymbol(const DataTypeSyntax* syntax, Scope* scope) {
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
            else if (dims.count() == 1 && dims[0].right == 0) {
                // if we have the common case of only one dimension and lsb == 0
                // then we can use the shared representation
                uint16_t width = dims[0].left.getAssertUInt16() + 1;
                return getIntegralType(width, isSigned, isFourState, isReg);
            }
            else {
                SmallVectorSized<int, 4> lowerBounds;
                SmallVectorSized<int, 4> widths;
                uint16_t totalWidth = 0;
                for (auto& dim : dims) {
                    uint16_t msb = dim.left.getAssertUInt16();
                    uint16_t lsb = dim.right.getAssertUInt16();
                    uint16_t width;
                    if (msb > lsb) {
                        width = msb - lsb + 1;
                        lowerBounds.append(lsb);
                    } else {
                        // TODO: msb == lsb
                        width = lsb - msb + 1;
                        lowerBounds.append(-lsb);
                    }
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
        case SyntaxKind::EnumType: {
            ExpressionBinder binder {*this, scope};
            const EnumTypeSyntax *enumSyntax = syntax->as<EnumTypeSyntax>();
            const IntegralTypeSymbol &baseType = (enumSyntax->baseType ? makeTypeSymbol(enumSyntax->baseType, scope) : getKnownType(SyntaxKind::IntType))->as<IntegralTypeSymbol>();

            SmallVectorSized<EnumValueSymbol *, 8> values;
            SVInt nextVal;
            for (auto member : enumSyntax->members) {
                //TODO: add each member to the scope
                if (member->initializer) {
                    ASSERT(member->initializer->expr);
                    auto bound = binder.bindConstantExpression(member->initializer->expr);
                    nextVal = std::get<SVInt>(evaluateConstant(bound));
                }
                EnumValueSymbol *valSymbol = alloc.emplace<EnumValueSymbol>(member->name.valueText(), member->name.location(), &baseType, nextVal);
                values.append(valSymbol);
                scope->add(valSymbol);
                ++nextVal;
            }
            return alloc.emplace<EnumTypeSymbol>(&baseType, enumSyntax->keyword.location(), values.copy(alloc));
        }
        case SyntaxKind::TypedefDeclaration: {
            auto tds = syntax->as<TypedefDeclarationSyntax>();
            auto type = makeTypeSymbol(tds->type, scope);
            return alloc.emplace<TypeAliasSymbol>(syntax, tds->name.location(), type, tds->name.valueText());
        }
        default:
            break;
    }

    // TODO: consider Void Type

    return getErrorType();
}

const SubroutineSymbol* SemanticModel::makeSubroutine(const FunctionDeclarationSyntax* syntax, Scope* scope) {
    auto proto = syntax->prototype;
    auto lifetime = getLifetime(proto->lifetime, VariableLifetime::Automatic);
    auto returnType = makeTypeSymbol(proto->returnType, scope);
    bool isTask = syntax->kind == SyntaxKind::TaskDeclaration;

    // For now only support simple function names
    auto name = proto->name->getFirstToken();
    auto funcScope = alloc.emplace<Scope>(scope);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;

    if (proto->portList) {
        const TypeSymbol* lastType = getKnownType(SyntaxKind::LogicType);
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto->portList->ports) {
            FormalArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword: direction = FormalArgumentDirection::In; break;
                case TokenKind::OutputKeyword: direction = FormalArgumentDirection::Out; break;
                case TokenKind::InOutKeyword: direction = FormalArgumentDirection::InOut; break;
                case TokenKind::RefKeyword:
                    if (portSyntax->constKeyword)
                        direction = FormalArgumentDirection::ConstRef;
                    else
                        direction = FormalArgumentDirection::Ref;
                    break;
                default:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
            }

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            const TypeSymbol* type;
            if (portSyntax->dataType)
                type = makeTypeSymbol(portSyntax->dataType, scope);
            else if (directionSpecified)
                type = getKnownType(SyntaxKind::LogicType);
            else
                type = lastType;

            auto declarator = portSyntax->declarator;

            arguments.append(alloc.emplace<FormalArgumentSymbol>(
                declarator->name,
                type,
                bindInitializer(declarator, type, scope),
                direction
            ));

            funcScope->add(arguments.back());

            lastDirection = direction;
            lastType = type;
        }
    }

    auto subroutine = alloc.emplace<SubroutineSymbol>(
        name,
        returnType,
        arguments.copy(alloc),
        lifetime,
        isTask,
        funcScope
    );

    ExpressionBinder binder { *this, subroutine };
    subroutine->body = binder.bindStatementList(syntax->items);
    return subroutine;
}

void SemanticModel::makeVariables(const DataDeclarationSyntax* syntax, SmallVector<const Symbol*>& results, Scope* scope) {
    // Just delegate to our internal function.
    // TODO: think about whether to just make that public instead
    handleDataDeclaration(syntax, results, scope);
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

void SemanticModel::evaluateParameter(ParameterSymbol* symbol, const ExpressionSyntax* initializer, Scope* scope) {
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

void SemanticModel::handlePackageImport(const PackageImportDeclarationSyntax* syntax, Scope* scope) {
    // add imported wildcard scopes as parents
    // for explicit imports create a scope specified items and add it as parent
    for (const PackageImportItemSyntax* item : syntax->items) {
        if (item->item.kind == TokenKind::Star) {
            const Symbol* pkgSym = packages.lookup(item->package.valueText());
            ASSERT(pkgSym && pkgSym->kind == SymbolKind::Module);
            scope->addParentScope(pkgSym->as<ModuleSymbol>().scope);
        }
        else if (item->item.kind == TokenKind::Identifier) {
            const Symbol* pkgSym = packages.lookup(item->package.valueText());
            ASSERT(pkgSym && pkgSym->kind == SymbolKind::Module);
            Scope* newScope = alloc.emplace<Scope>();
            newScope->add(pkgSym->as<ModuleSymbol>().scope->lookup(item->item.valueText()));
            scope->addParentScope(newScope);
        }
        else {
            ASSERT(false);
        }
    }
}

void SemanticModel::handleInstantiation(const HierarchyInstantiationSyntax* syntax, SmallVector<const Symbol*>& results, Scope* instantiationScope) {
    // Try to find the module/interface/program being instantiated; we can't do anything without it.
    // We've already reported an error for missing modules.
    const ModuleDeclarationSyntax* decl = declTable.find(syntax->type.valueText());
    if (!decl)
        return;

    // Evaluate public parameter assignments
    for (const HierarchicalInstanceSyntax* instance : syntax->instances) {
        Scope* scope = alloc.emplace<Scope>();
        scope->addParentScope(instantiationScope);
        // get interface objects for this instance
        makeInterfacePorts(scope, decl, instance, instantiationScope, syntax->getFirstToken().location());
        makePublicParameters(scope, decl, syntax->parameters, instantiationScope, syntax->getFirstToken().location(), false);
        const ModuleSymbol* module = makeModule(decl, scope);
        const InstanceSymbol *instSym = nullptr;
        if (instance->dimensions.count() == 0) {
            instSym = alloc.emplace<InstanceSymbol>(module, instance->name.valueText(), syntax->type.location(), false);
        }
        else {
            // figure out dimensions of the instance array
            SmallVectorSized<ConstantRange, 2> dims;
            ExpressionBinder binder { *this, scope };
            for (const VariableDimensionSyntax* dim : instance->dimensions) {
                if (!dim->specifier) {
                    dims.emplace(ConstantRange{SVInt{0}, SVInt{0}});
                    break;
                }
                if (dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier) {
                    auto& diag = diagnostics.add(DiagCode::UnpackedDimensionRequired, dim->specifier->getFirstToken().location());
                    diag << dim->specifier->sourceRange();
                    return;
                }
                auto selector = dim->specifier->as<RangeDimensionSpecifierSyntax>()->selector;
                ASSERT(selector);
                switch (selector->kind) {
                    case SyntaxKind::SimpleRangeSelect: {
                        auto left = selector->as<RangeSelectSyntax>()->left;
                        ASSERT(left);
                        auto leftBound = binder.bindConstantExpression(left);
                        auto leftValue = evaluateConstant(leftBound);
                        if (!left || leftBound->bad() || leftValue.bad()) {
                            auto& diag = diagnostics.add(DiagCode::UnpackedDimensionRequiresConstRange, left->getFirstToken().location());
                            diag << left->sourceRange();
                            return;

                        }
                        auto right = selector->as<RangeSelectSyntax>()->right;
                        ASSERT(right);
                        auto rightBound = binder.bindConstantExpression(right);
                        auto rightValue = evaluateConstant(rightBound);
                        if (!right || rightBound->bad() || rightValue.bad()) {
                            auto& diag = diagnostics.add(DiagCode::UnpackedDimensionRequiresConstRange, right->getFirstToken().location());
                            diag << right->sourceRange();
                            return;

                        }
                        dims.emplace(ConstantRange{std::get<SVInt>(leftValue), std::get<SVInt>(rightValue)});
                        break;
                    }
                    case SyntaxKind::BitSelect: {
                        auto expr = selector->as<BitSelectSyntax>()->expr;
                        ASSERT(expr);
                        auto exprBound = binder.bindConstantExpression(expr);
                        auto exprValue = evaluateConstant(exprBound);
                        if (!expr || exprBound->bad() || exprValue.bad()) {
                            auto& diag = diagnostics.add(DiagCode::UnpackedDimensionRequiresConstRange, expr->getFirstToken().location());
                            diag << expr->sourceRange();
                            return;

                        }
                        dims.emplace(ConstantRange{std::get<SVInt>(exprValue), std::get<SVInt>(exprValue)});
                        break;
                    }
                    default: {
                        auto& diag = diagnostics.add(DiagCode::UnpackedDimensionRequired, selector->getFirstToken().location());
                        diag << selector->sourceRange();
                        return;
                    }
                }
            }
            // load all interface ports into scope
            // TODO: arrayed interface expressions must match
            instSym = alloc.emplace<InstanceSymbol>(module, instance->name.valueText(), syntax->type.location(), false, dims.copy(alloc));
        };
        results.append(instSym);
        instantiationScope->add(instSym);
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

void SemanticModel::handleLoopGenerate(const LoopGenerateSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope) {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    // Initialize the genvar
    auto initial = evaluateConstant(syntax->initialExpr, scope);
    if (!initial)
        return;

    // Fabricate a local variable that will serve as the loop iteration variable.
    Scope iterScope { scope };
    VariableSymbol local { syntax->identifier, getKnownType(SyntaxKind::IntType) };
    iterScope.add(&local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    auto stopExpr = bindConstantExpression(syntax->stopExpr, &iterScope);
    auto iterExpr = bindConstantExpression(syntax->iterationExpr, &iterScope);

    // Create storage for the iteration variable.
    ConstantEvaluator ce;
    auto& genvar = ce.createTemporary(&local);

    // Generate blocks!
    for (genvar = initial; ce.evaluateBool(stopExpr); ce.evaluateExpr(iterExpr)) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        Scope localScope { &iterScope };
        ParameterSymbol iterParam {
            syntax->identifier.valueText(),
            syntax->identifier.location(), nullptr, true
        };
        iterParam.value = genvar;
        localScope.add(&iterParam);

        handleGenerateBlock(syntax->block, results, &localScope);
    }
}

void SemanticModel::handleGenerateBlock(const MemberSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* _scope) {
    Scope *scope = alloc.emplace<Scope>(_scope);
    if (syntax->kind == SyntaxKind::GenerateBlock) {
        SmallVectorSized<const Symbol*, 8> children;
        for (const MemberSyntax* member : syntax->as<GenerateBlockSyntax>()->members) {
            handleGenerateItem(member, children, scope);
        }
        results.append(alloc.emplace<GenerateBlock>(children.copy(alloc), scope));
    }
    else {
        handleGenerateItem(syntax, results, scope);
    }
}

static ProceduralBlock::Kind proceduralBlockKindFromKeyword(Token kindKeyword) {
    switch (kindKeyword.kind) {
        case TokenKind::InitialKeyword: return ProceduralBlock::Initial;
        case TokenKind::FinalKeyword:   return ProceduralBlock::Final;
        case TokenKind::AlwaysKeyword:  return ProceduralBlock::Always;
        case TokenKind::AlwaysCombKeyword:  return ProceduralBlock::AlwaysComb;
        case TokenKind::AlwaysFFKeyword:  return ProceduralBlock::AlwaysFF;
        case TokenKind::AlwaysLatchKeyword:  return ProceduralBlock::AlwaysLatch;
        default:
            ASSERT(false, "Unknown ProceduralBlock kind keyword: %s",
                   kindKeyword.toString().c_str());
            return ProceduralBlock::Initial;    // silence warnings
    }
}

void SemanticModel::handleProceduralBlock(const ProceduralBlockSyntax *syntax, SmallVector<const Symbol *>& results, const Scope* _scope) {
    Scope *scope = alloc.emplace<Scope>(_scope);
    SmallVectorSized<const Symbol*, 2> children;
    //TODO handleStatement(syntax->statement, children, scope);
    results.append(alloc.emplace<ProceduralBlock>(
        children.copy(alloc), proceduralBlockKindFromKeyword(syntax->keyword), scope));
}

void SemanticModel::handleDataDeclaration(const DataDeclarationSyntax *syntax, SmallVector<const Symbol *>& results, Scope* scope) {
    VariableSymbol::Modifiers modifiers;
    for (auto token : syntax->modifiers) {
        switch(token.kind) {
            case TokenKind::ConstKeyword:
                modifiers.constM = 1;
                break;
            case TokenKind::VarKeyword:
                modifiers.varM = 1;
                break;
            case TokenKind::StaticKeyword:
                modifiers.staticM = 1;
                break;
            case TokenKind::AutomaticKeyword:
                modifiers.automaticM = 1;
                break;
            default:
                ASSERT(false, "Unknown variable modifier: %s", token.toString().c_str());
                break;
        }
    }
    const TypeSymbol *typeSymbol = makeTypeSymbol(syntax->type, scope);

    for (auto varDeclarator : syntax->declarators) {
        handleVariableDeclarator(varDeclarator, results, scope, modifiers, typeSymbol);
    }
}

void SemanticModel::handleVariableDeclarator(const VariableDeclaratorSyntax *syntax, SmallVector<const Symbol *>& results, Scope *scope, const VariableSymbol::Modifiers &modifiers, const TypeSymbol *typeSymbol) {
    ASSERT(typeSymbol);
    // TODO handle dimensions
    Symbol *dataSymbol = alloc.emplace<VariableSymbol>(syntax->name, typeSymbol, bindInitializer(syntax, typeSymbol, scope), modifiers);
    results.append(dataSymbol);
    scope->add(dataSymbol);
}

void SemanticModel::handleGenerateItem(const MemberSyntax* syntax, SmallVector<const Symbol*>& results, Scope* scope) {
    switch (syntax->kind) {
        case SyntaxKind::HierarchyInstantiation:
            handleInstantiation(syntax->as<HierarchyInstantiationSyntax>(), results, scope);
            break;
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock:
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::AlwaysLatchBlock:
            handleProceduralBlock(syntax->as<ProceduralBlockSyntax>(), results, scope);
            break;
        case SyntaxKind::DataDeclaration:
            handleDataDeclaration(syntax->as<DataDeclarationSyntax>(), results, scope);
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            results.append(makeSubroutine(syntax->as<FunctionDeclarationSyntax>(), scope));
            break;

            DEFAULT_UNREACHABLE;
    }
}

void SemanticModel::handleGenvarDecl(const GenvarDeclarationSyntax* syntax, SmallVector<const Symbol*>& results, const Scope* scope) {
    for (auto identifierSyntax : syntax->identifiers) {
        auto name = identifierSyntax->identifier;
        if (!name.valueText())
            continue;

        results.append(alloc.emplace<GenvarSymbol>(name.valueText(), name.location()));
    }
}

void SemanticModel::makePublicParameters(Scope* declScope, const ModuleDeclarationSyntax* decl,
                                         const ParameterValueAssignmentSyntax* parameterAssignments,
                                         Scope* instantiationScope, SourceLocation instanceLocation, bool isTopLevel) {
    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<const ParameterSymbol*, 8> results;
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
    for (auto import : decl->header->imports) {
        handlePackageImport(import, declScope);
    }
    // also find direct body imports
    // TODO: check location of import vs usage
    for (const MemberSyntax* member : decl->members) {
        if (member->kind == SyntaxKind::PackageImportDeclaration) {
            handlePackageImport(member->as<PackageImportDeclarationSyntax>(), declScope);
        }
    }

    const auto& moduleParamInfo = getModuleParams(decl);
    for (const auto& info : moduleParamInfo) {
        ParameterSymbol* symbol = alloc.emplace<ParameterSymbol>(info.name, info.location, info.paramDecl, info.local);
        results.append(symbol);
        declScope->add(symbol);
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
            Scope* scope;
            if (info.local || orderedIndex >= orderedParams.count()) {
                initializer = info.initializer;
                scope = declScope;
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
            Scope* scope = nullptr;
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
                scope = declScope;
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

// create all interface objects for a particular module instance and load them into scope
void SemanticModel::makeInterfacePorts(Scope* scope,
                                       const ModuleDeclarationSyntax* instanceModuleSyntax,
                                       const HierarchicalInstanceSyntax* syntax,
                                       const Scope* instantiationScope,
                                       SourceLocation instanceLocation)
{
    std::vector<StringRef> portNames;
    std::unordered_set<StringRef> ifPortNames;
    // port declarations in header
    auto debugStr = ((ModuleDeclarationSyntax*)instanceModuleSyntax)->toString();
    ASSERT(instanceModuleSyntax->header);
    if (!instanceModuleSyntax->header->ports) return;
    if (instanceModuleSyntax->header->ports->kind == SyntaxKind::AnsiPortList) {
        ExpressionBinder binder { *this, scope };
        auto ports = instanceModuleSyntax->header->ports->as<AnsiPortListSyntax>()->ports;
        for (auto port : ports) {
            ASSERT(port->kind == SyntaxKind::ImplicitAnsiPort); // everything else is invalid
            auto type = port->as<ImplicitAnsiPortSyntax>();
            auto delc = port->as<ImplicitAnsiPortSyntax>()->declarator;
            portNames.emplace_back(delc->name.valueText());
            switch (type->header->kind) {
                case SyntaxKind::InterfacePortHeader: {
                    auto ifType = type->header->as<InterfacePortHeaderSyntax>();
                    ASSERT(ifType->nameOrKeyword.kind != TokenKind::InterfaceKeyword); // TODO: add support for generic interface ports
                    // TODO: technically the interface should be looked up in the scope of the instance module,
                    // TODO: but since we are connecting it, it should also be visible in the instance
                    auto typeSym = instantiationScope->lookup(ifType->nameOrKeyword.valueText());
                    ASSERT(typeSym && typeSym->kind == SymbolKind::Module); // TODO: emit diag about unknown interface
                    //auto modportSym = typeSym->as<ModuleSymbol>().scope->lookup(ifType->modport->member.valueText());
                    //ASSERT(modportSym && modportSym->kind == SymbolKind::Modport); // TODO: emit diag about unknown modport
                    ifPortNames.emplace(delc->name.valueText());
                    break;
                }
                case SyntaxKind::VariablePortHeader: {
                    auto ifType = type->header->as<VariablePortHeaderSyntax>();
                    if (ifType->direction) continue; // not an interface
                    if (ifType->varKeyword) continue; // TODO: check for interface keyword
                    if (ifType->type->kind != SyntaxKind::NamedType) continue;
                    auto name = ifType->type->as<NamedTypeSyntax>()->name;
                    const Symbol *typeSym = nullptr;
                    switch (name->kind) {
                        case SyntaxKind::IdentifierName: {
                            // TODO: need to lookup the name of the interface in the scope of the module which is empty
                            typeSym = instantiationScope->lookup(name->as<IdentifierNameSyntax>()->identifier.valueText());
                            break;
                        }
                        case SyntaxKind::ScopedName: {
                            auto boundExpr = binder.bindSelfDeterminedExpression(name->as<ScopedNameSyntax>());
                            typeSym = boundExpr->type;
                            break;
                        }
                        default:
                            continue;
                    }
                    ASSERT(typeSym && typeSym->kind == SymbolKind::Module); // TODO: emit diag about unknown interface
                    ifPortNames.emplace(delc->name.valueText());
                    break;
                }
            }
        }
    }
    // port names in header
    // port declarations in body
    else if (instanceModuleSyntax->header->ports->kind == SyntaxKind::NonAnsiPortList) {
        auto ports = instanceModuleSyntax->header->ports->as<NonAnsiPortListSyntax>()->ports;
        for (auto port : ports) {
            ASSERT(port->kind == SyntaxKind::ImplicitNonAnsiPort); // TODO: add support for port expressions
            auto expr = port->as<ImplicitNonAnsiPortSyntax>()->expr;
            ASSERT(expr->kind == SyntaxKind::IdentifierName); // everything else is invalid
            portNames.emplace_back(expr->as<IdentifierNameSyntax>()->identifier.valueText());
        }
        for (auto member : instanceModuleSyntax->members) {
            if (member->kind == SyntaxKind::PortDeclaration) {
                for (auto decl : member->as<PortDeclarationSyntax>()->declarators) {
                    // TODO: emit diag about a port decl for name not listed in non-ansi header
                    ASSERT(std::find(portNames.begin(), portNames.end(), decl->name.valueText()) != portNames.end());
                }
            }
        }
    }

    // gather port mappings
    size_t portIndex = 0;
    bool hasOrdered = false;
    bool hasNamed = false;
    bool hasWild = false;
    std::unordered_map<StringRef, const ExpressionSyntax*> ifPortMap;
    for (auto conn : syntax->connections) {
        switch (conn->kind) {
            case SyntaxKind::OrderedPortConnection: {
                auto ordered = conn->as<OrderedPortConnectionSyntax>();
                ASSERT(!hasNamed); // TODO: emit diag about mixing
                ASSERT(portIndex < portNames.size()); // TODO: emit diag about too many ordered port connections
                auto name = portNames[portIndex++];
                if (!ifPortNames.count(name)) continue;
                ifPortMap.emplace(name, ordered->expr);
                hasOrdered = true;
                break;
            }
            case SyntaxKind::NamedPortConnection: {
                auto named = conn->as<NamedPortConnectionSyntax>();
                auto name = named->name.valueText();
                if (!ifPortNames.count(name)) continue;
                ASSERT(!hasOrdered); // TODO: emit diag about mixing
                ifPortMap.emplace(name, named->connection->expression);
                hasNamed = true;
                break;
            }
            case SyntaxKind::WildcardPortConnection:
                hasWild = true;
                break;

            default:
                ASSERT(false); // impossible
        }
    }

    // process interface port mapping to Interface or InterfaceArray symbols
    for (auto conn : ifPortMap) {
        ASSERT(conn.second->kind == SyntaxKind::IdentifierName); // TODO: handle more complex expressions like array select
        auto sym = instantiationScope->lookup(conn.second->as<IdentifierNameSyntax>()->identifier.valueText());
        ASSERT(sym && sym->kind == SymbolKind::Instance);
        auto instSym = sym->as<InstanceSymbol>();
        scope->add(alloc.emplace<InstanceSymbol>(instSym.module, conn.first, conn.second->as<IdentifierNameSyntax>()->identifier.location(), false));
    }
    if (hasWild) {
        for (auto name : ifPortNames) {
            if (!ifPortMap.count(name)) {
                auto sym = instantiationScope->lookup(name);
                ASSERT(sym && sym->kind == SymbolKind::Instance);
                auto instSym = sym->as<InstanceSymbol>();
                scope->add(alloc.emplace<InstanceSymbol>(instSym.module, instSym.name, SourceLocation(), false)); // TODO: add location of the port name
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

const BoundExpression* SemanticModel::bindInitializer(const VariableDeclaratorSyntax *syntax, const TypeSymbol* type, const Scope* scope) {
    if (!syntax->initializer)
        return nullptr;

    ExpressionBinder binder { *this, scope };
    return binder.bindAssignmentLikeContext(syntax->initializer->expr, syntax->name.location(), type);
}

const BoundExpression* SemanticModel::bindConstantExpression(const ExpressionSyntax* syntax, const Scope* scope) {
    ExpressionBinder binder { *this, scope };
    return binder.bindConstantExpression(syntax);
}

ConstantValue SemanticModel::evaluateConstant(const ExpressionSyntax* syntax, const Scope* scope) {
    auto expr = bindConstantExpression(syntax, scope);
    if (expr->bad())
        return nullptr;

    return evaluateConstant(expr);
}

ConstantValue SemanticModel::evaluateConstant(const BoundExpression* tree) {
    // TODO: eventually this will need diagnostics and other stuff
    ConstantEvaluator evaluator;
    return evaluator.evaluateExpr(tree);
}

}
