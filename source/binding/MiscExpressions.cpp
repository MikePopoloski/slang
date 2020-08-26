//------------------------------------------------------------------------------
// MiscExpressions.cpp
// Definitions for miscellaneous expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/MiscExpressions.h"

#include "slang/binding/SelectExpressions.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

Expression& NamedValueExpression::fromSymbol(const BindContext& context, const Symbol& symbol,
                                             bool isHierarchical, SourceRange sourceRange) {
    Compilation& compilation = context.getCompilation();
    if (!symbol.isValue()) {
        context.addDiag(diag::NotAValue, sourceRange) << symbol.name;
        return badExpr(compilation, nullptr);
    }

    if ((context.flags & BindFlags::StaticInitializer) != 0 &&
        VariableSymbol::isKind(symbol.kind) &&
        symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
        context.addDiag(diag::AutoFromStaticInit, sourceRange) << symbol.name;
        return badExpr(compilation, nullptr);
    }

    return *compilation.emplace<NamedValueExpression>(symbol.as<ValueSymbol>(), isHierarchical,
                                                      sourceRange);
}

ConstantValue NamedValueExpression::evalImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    switch (symbol.kind) {
        case SymbolKind::Parameter:
            return symbol.as<ParameterSymbol>().getValue();
        case SymbolKind::EnumValue:
            return symbol.as<EnumValueSymbol>().getValue();
        default:
            ConstantValue* v = context.findLocal(&symbol);
            if (v)
                return *v;
            break;
    }

    // If we reach this point, the variable was not found, which should mean that
    // it's not actually constant.
    auto& diag = context.addDiag(diag::ConstEvalNonConstVariable, sourceRange) << symbol.name;
    diag.addNote(diag::NoteDeclarationHere, symbol.location);
    return nullptr;
}

LValue NamedValueExpression::evalLValueImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    auto cv = context.findLocal(&symbol);
    if (!cv) {
        auto& diag = context.addDiag(diag::ConstEvalNonConstVariable, sourceRange) << symbol.name;
        diag.addNote(diag::NoteDeclarationHere, symbol.location);
        return nullptr;
    }

    return LValue(*cv);
}

bool NamedValueExpression::verifyConstantImpl(EvalContext& context) const {
    if (context.isScriptEval())
        return true;

    // Hierarchical names are disallowed in constant expressions and constant functions
    if (isHierarchical) {
        context.addDiag(diag::ConstEvalHierarchicalNameInCE, sourceRange) << symbol.name;
        return false;
    }

    const EvalContext::Frame& frame = context.topFrame();
    const SubroutineSymbol* subroutine = frame.subroutine;
    if (!subroutine)
        return true;

    // Constant functions have a bunch of additional restrictions. See [13.4.4]:
    // - All parameter values used within the function shall be defined before the use of
    //   the invoking constant function call.
    // - All identifiers that are not parameters or functions shall be declared locally to
    //   the current function.
    if (symbol.kind != SymbolKind::Parameter && symbol.kind != SymbolKind::EnumValue) {
        const Scope* scope = symbol.getParentScope();
        while (scope && scope != subroutine)
            scope = scope->asSymbol().getParentScope();

        if (scope != subroutine) {
            auto& diag =
                context.addDiag(diag::ConstEvalFunctionIdentifiersMustBeLocal, sourceRange);
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }
    else {
        // If the two locations are not in the same compilation unit, assume that it's ok.
        auto compare = symbol.isDeclaredBefore(frame.lookupLocation);
        if (!compare.value_or(true)) {
            auto& diag = context.addDiag(diag::ConstEvalIdUsedInCEBeforeDecl, sourceRange)
                         << symbol.name;
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }

    return true;
}

bool NamedValueExpression::verifyAssignableImpl(const BindContext& context, bool isNonBlocking,
                                                SourceLocation location) const {
    if (symbol.kind == SymbolKind::Parameter || symbol.kind == SymbolKind::EnumValue) {
        auto& diag = context.addDiag(diag::ExpressionNotAssignable, location);
        diag.addNote(diag::NoteDeclarationHere, symbol.location);
        diag << sourceRange;
        return false;
    }

    if (VariableSymbol::isKind(symbol.kind)) {
        auto& var = symbol.as<VariableSymbol>();
        if (var.isConstant) {
            auto& diag = context.addDiag(diag::AssignmentToConst, location);
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
            diag << symbol.name << sourceRange;
            return false;
        }

        if (isNonBlocking && var.lifetime == VariableLifetime::Automatic) {
            auto& diag = context.addDiag(diag::NonblockingAssignmentToAuto, location);
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
            diag << symbol.name << sourceRange;
            return false;
        }
    }

    return true;
}

void NamedValueExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("symbol", symbol);
    serializer.write("isHierarchical", isHierarchical);
}

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const InvocationExpressionSyntax& syntax,
                                       const BindContext& context) {
    if (syntax.left->kind == SyntaxKind::MemberAccessExpression) {
        return MemberAccessExpression::fromSyntax(
            compilation, syntax.left->as<MemberAccessExpressionSyntax>(), &syntax, context);
    }

    if (!NameSyntax::isKind(syntax.left->kind)) {
        SourceLocation loc = syntax.arguments ? syntax.arguments->openParen.location()
                                              : syntax.left->getFirstToken().location();
        auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
        diag << syntax.left->sourceRange();
        return badExpr(compilation, nullptr);
    }

    return bindName(compilation, syntax.left->as<NameSyntax>(), &syntax, context);
}

Expression& CallExpression::fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                       const InvocationExpressionSyntax* syntax, SourceRange range,
                                       const BindContext& context) {
    if (subroutine.index() == 1) {
        const SystemCallInfo& info = std::get<1>(subroutine);
        return createSystemCall(compilation, *info.subroutine, nullptr, syntax, range, context);
    }

    // Collect all arguments into a list of ordered expressions (which can
    // optionally be nullptr to indicate an empty argument) and a map of
    // named argument assignments.
    SmallVectorSized<const SyntaxNode*, 8> orderedArgs;
    SmallMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedArgs;

    if (syntax && syntax->arguments) {
        for (auto arg : syntax->arguments->parameters) {
            if (arg->kind == SyntaxKind::NamedArgument) {
                const NamedArgumentSyntax& nas = arg->as<NamedArgumentSyntax>();
                auto name = nas.name.valueText();
                if (!name.empty()) {
                    auto pair = namedArgs.emplace(name, std::make_pair(&nas, false));
                    if (!pair.second) {
                        auto& diag =
                            context.addDiag(diag::DuplicateArgAssignment, nas.name.location());
                        diag << name;
                        diag.addNote(diag::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
            else {
                // Once a named argument has been seen, no more ordered arguments are allowed.
                if (!namedArgs.empty()) {
                    context.addDiag(diag::MixingOrderedAndNamedArgs,
                                    arg->getFirstToken().location());
                    return badExpr(compilation, nullptr);
                }

                if (arg->kind == SyntaxKind::EmptyArgument)
                    orderedArgs.append(arg);
                else
                    orderedArgs.append(arg->as<OrderedArgumentSyntax>().expr);
            }
        }
    }

    // Now bind all arguments.
    bool bad = false;
    uint32_t orderedIndex = 0;
    SmallVectorSized<const Expression*, 8> boundArgs;
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);

    for (auto formal : symbol.arguments) {
        const Expression* expr = nullptr;
        if (orderedIndex < orderedArgs.size()) {
            auto arg = orderedArgs[orderedIndex++];
            if (arg->kind == SyntaxKind::EmptyArgument) {
                // Empty arguments are allowed as long as a default is provided.
                expr = formal->getInitializer();
                if (!expr)
                    context.addDiag(diag::ArgCannotBeEmpty, arg->sourceRange()) << formal->name;
            }
            else {
                expr = &Expression::bindArgument(formal->getType(), formal->direction,
                                                 arg->as<ExpressionSyntax>(), context);
            }

            // Make sure there isn't also a named value for this argument.
            if (auto it = namedArgs.find(formal->name); it != namedArgs.end()) {
                auto& diag = context.addDiag(diag::DuplicateArgAssignment,
                                             it->second.first->name.location());
                diag << formal->name;
                diag.addNote(diag::NotePreviousUsage, arg->getFirstToken().location());
                it->second.second = true;
                bad = true;
            }
        }
        else if (auto it = namedArgs.find(formal->name); it != namedArgs.end()) {
            // Mark this argument as used so that we can later detect if
            // any were unused.
            it->second.second = true;

            auto arg = it->second.first->expr;
            if (!arg) {
                // Empty arguments are allowed as long as a default is provided.
                expr = formal->getInitializer();
                if (!expr) {
                    context.addDiag(diag::ArgCannotBeEmpty, it->second.first->sourceRange())
                        << formal->name;
                }
            }
            else {
                expr =
                    &Expression::bindArgument(formal->getType(), formal->direction, *arg, context);
            }
        }
        else {
            expr = formal->getInitializer();
            if (!expr) {
                if (namedArgs.empty()) {
                    auto& diag = context.addDiag(diag::TooFewArguments, range);
                    diag << symbol.arguments.size() << orderedArgs.size();
                    bad = true;
                    break;
                }
                else {
                    context.addDiag(diag::UnconnectedArg, range) << formal->name;
                }
            }
        }

        if (!expr) {
            bad = true;
        }
        else {
            bad |= expr->bad();
            boundArgs.append(expr);
        }
    }

    // Make sure there weren't too many ordered arguments provided.
    if (orderedIndex < orderedArgs.size()) {
        auto& diag = context.addDiag(diag::TooManyArguments, range);
        diag << symbol.arguments.size();
        diag << orderedArgs.size();
        bad = true;
    }

    for (const auto& pair : namedArgs) {
        // We marked all the args that we used, so anything left over is an arg assignment
        // for a non-existent arg.
        if (!pair.second.second) {
            auto& diag = context.addDiag(diag::ArgDoesNotExist, pair.second.first->name.location());
            diag << pair.second.first->name.valueText();
            diag << symbol.name;
            bad = true;
        }
    }

    auto result = compilation.emplace<CallExpression>(&symbol, symbol.getReturnType(),
                                                      boundArgs.copy(compilation),
                                                      context.lookupLocation, range);
    if (syntax)
        context.setAttributes(*result, syntax->attributes);

    if (bad)
        return badExpr(compilation, result);

    return *result;
}

Expression& CallExpression::fromSystemMethod(Compilation& compilation, const Expression& expr,
                                             const LookupResult::MemberSelector& selector,
                                             const InvocationExpressionSyntax* syntax,
                                             const BindContext& context) {
    const Type& type = expr.type->getCanonicalType();
    auto subroutine = compilation.getSystemMethod(type.kind, selector.name);
    if (!subroutine) {
        if (syntax) {
            context.addDiag(diag::UnknownSystemMethod, selector.nameRange)
                << selector.name << *expr.type;
        }
        else {
            auto& diag = context.addDiag(diag::InvalidMemberAccess, selector.dotLocation);
            diag << expr.sourceRange;
            diag << selector.nameRange;
            diag << *expr.type;
        }
        return badExpr(compilation, &expr);
    }

    return createSystemCall(compilation, *subroutine, &expr, syntax,
                            syntax ? syntax->sourceRange() : expr.sourceRange, context);
}

Expression& CallExpression::createSystemCall(Compilation& compilation,
                                             const SystemSubroutine& subroutine,
                                             const Expression* firstArg,
                                             const InvocationExpressionSyntax* syntax,
                                             SourceRange range, const BindContext& context) {
    SmallVectorSized<const Expression*, 8> buffer;
    if (firstArg)
        buffer.append(firstArg);

    if (syntax && syntax->arguments) {
        auto actualArgs = syntax->arguments->parameters;
        for (size_t i = 0; i < actualArgs.size(); i++) {
            size_t index = i + (firstArg ? 1 : 0);
            switch (actualArgs[i]->kind) {
                case SyntaxKind::OrderedArgument: {
                    const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
                    buffer.append(&subroutine.bindArgument(index, context, *arg.expr, buffer));
                    break;
                }
                case SyntaxKind::NamedArgument:
                    context.addDiag(diag::NamedArgNotAllowed, actualArgs[i]->sourceRange());
                    return badExpr(compilation, nullptr);
                case SyntaxKind::EmptyArgument:
                    if (subroutine.allowEmptyArgument(index)) {
                        buffer.append(compilation.emplace<EmptyArgumentExpression>(
                            compilation.getVoidType(), actualArgs[i]->sourceRange()));
                    }
                    else {
                        context.addDiag(diag::EmptyArgNotAllowed, actualArgs[i]->sourceRange());
                        return badExpr(compilation, nullptr);
                    }
                    break;
                default:
                    THROW_UNREACHABLE;
            }
        }
    }

    SystemCallInfo callInfo{ &subroutine, &context.scope };
    const Type& type = subroutine.checkArguments(context, buffer, range);
    auto expr = compilation.emplace<CallExpression>(callInfo, type, buffer.copy(compilation),
                                                    context.lookupLocation, range);

    if (type.isError())
        return badExpr(compilation, expr);

    for (auto arg : expr->arguments()) {
        if (arg->bad())
            return badExpr(compilation, expr);
    }

    if (syntax)
        context.setAttributes(*expr, syntax->attributes);

    return *expr;
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Delegate system calls to their appropriate handler.
    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->eval(*callInfo.scope, context, arguments());
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!checkConstant(context, symbol, sourceRange))
        return nullptr;

    // Evaluate all argument in the current stack frame.
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments()) {
        ConstantValue v = arg->eval(context);
        if (!v)
            return nullptr;
        args.emplace(std::move(v));
    }

    // Push a new stack frame, push argument values as locals.
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return nullptr;

    span<const FormalArgumentSymbol* const> formals = symbol.arguments;
    for (size_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    context.createLocal(symbol.returnValVar);

    using ER = Statement::EvalResult;
    ER er = symbol.getBody(&context).eval(context);

    // If we got a disable result, it means a disable statement was evaluated that
    // targeted a block that wasn't executing. This isn't allowed in a constant expression.
    // Handle this before popping the frame so that we get the stack reported.
    if (er == ER::Disable)
        context.addDiag(diag::ConstEvalDisableTarget, context.getDisableRange());

    ConstantValue result = std::move(*context.findLocal(symbol.returnValVar));
    context.popFrame();

    if (er == ER::Fail || er == ER::Disable)
        return nullptr;

    ASSERT(er == ER::Success || er == ER::Return);
    return result;
}

bool CallExpression::verifyConstantImpl(EvalContext& context) const {
    for (auto arg : arguments()) {
        if (!arg->verifyConstant(context))
            return false;
    }

    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->verifyConstant(context, arguments(), sourceRange);
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!checkConstant(context, symbol, sourceRange))
        return false;

    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return false;

    bool result = symbol.getBody(&context).verifyConstant(context);
    context.popFrame();
    return result;
}

bool CallExpression::checkConstant(EvalContext& context, const SubroutineSymbol& subroutine,
                                   SourceRange range) {
    if (context.isScriptEval())
        return true;

    if (subroutine.subroutineKind == SubroutineKind::Task) {
        context.addDiag(diag::ConstEvalTaskNotConstant, range);
        return false;
    }

    if (subroutine.getReturnType().isVoid()) {
        context.addDiag(diag::ConstEvalVoidNotConstant, range);
        return false;
    }

    for (auto arg : subroutine.arguments) {
        if (arg->direction != ArgumentDirection::In) {
            context.addDiag(diag::ConstEvalFunctionArgDirection, range);
            return false;
        }
    }

    auto scope = subroutine.getParentScope();
    ASSERT(scope);
    if (scope->asSymbol().kind == SymbolKind::GenerateBlock) {
        context.addDiag(diag::ConstEvalFunctionInsideGenerate, range);
        return false;
    }

    return true;
}

string_view CallExpression::getSubroutineName() const {
    if (subroutine.index() == 1) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->name;
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    return symbol.name;
}

SubroutineKind CallExpression::getSubroutineKind() const {
    if (subroutine.index() == 1) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->kind;
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    return symbol.subroutineKind;
}

void CallExpression::serializeTo(ASTSerializer& serializer) const {
    if (subroutine.index() == 1) {
        auto& callInfo = std::get<1>(subroutine);
        serializer.write("subroutine", callInfo.subroutine->name);
    }
    else {
        const SubroutineSymbol& symbol = *std::get<0>(subroutine);
        serializer.writeLink("subroutine", symbol);
    }

    if (!arguments().empty()) {
        serializer.startArray("arguments");
        for (auto arg : arguments())
            serializer.serialize(*arg);
        serializer.endArray();
    }
}

Expression& DataTypeExpression::fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                           const BindContext& context) {
    if ((context.flags & BindFlags::AllowDataType) == 0) {
        context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    const Type& type = compilation.getType(syntax, context.lookupLocation, context.scope);
    return *compilation.emplace<DataTypeExpression>(type, syntax.sourceRange());
}

Expression& HierarchicalReferenceExpression::fromSyntax(Compilation& compilation,
                                                        const NameSyntax& syntax,
                                                        const BindContext& context) {
    LookupResult result;
    Lookup::name(context.scope, syntax, context.lookupLocation, LookupFlags::AllowDeclaredAfter,
                 result);

    if (result.hasError())
        compilation.addDiagnostics(result.getDiagnostics());

    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(compilation, nullptr);

    return *compilation.emplace<HierarchicalReferenceExpression>(*symbol, compilation.getVoidType(),
                                                                 syntax.sourceRange());
}

void HierarchicalReferenceExpression::serializeTo(ASTSerializer& serializer) const {
    if (symbol)
        serializer.writeLink("symbol", *symbol);
}

Expression& MinTypMaxExpression::fromSyntax(Compilation& compilation,
                                            const MinTypMaxExpressionSyntax& syntax,
                                            const BindContext& context,
                                            const Type* assignmentTarget) {
    // Only one of the expressions will be considered evaluated.
    auto minFlags = BindFlags::UnevaluatedBranch;
    auto typFlags = BindFlags::UnevaluatedBranch;
    auto maxFlags = BindFlags::UnevaluatedBranch;
    switch (compilation.getOptions().minTypMax) {
        case MinTypMax::Min:
            minFlags = BindFlags::None;
            break;
        case MinTypMax::Typ:
            typFlags = BindFlags::None;
            break;
        case MinTypMax::Max:
            maxFlags = BindFlags::None;
            break;
    }

    auto& min = create(compilation, *syntax.min, context, minFlags, assignmentTarget);
    auto& typ = create(compilation, *syntax.typ, context, typFlags, assignmentTarget);
    auto& max = create(compilation, *syntax.max, context, maxFlags, assignmentTarget);

    Expression* selected = nullptr;
    switch (compilation.getOptions().minTypMax) {
        case MinTypMax::Min:
            selected = &min;
            break;
        case MinTypMax::Typ:
            selected = &typ;
            break;
        case MinTypMax::Max:
            selected = &max;
            break;
    }

    auto result = compilation.emplace<MinTypMaxExpression>(*selected->type, min, typ, max, selected,
                                                           syntax.sourceRange());
    if (min.bad() || typ.bad() || max.bad())
        return badExpr(compilation, result);

    return *result;
}

bool MinTypMaxExpression::propagateType(const BindContext& context, const Type& newType) {
    // Only the selected expression gets a propagated type.
    type = &newType;
    contextDetermined(context, selected_, newType);
    return true;
}

ConstantValue MinTypMaxExpression::evalImpl(EvalContext& context) const {
    return selected().eval(context);
}

bool MinTypMaxExpression::verifyConstantImpl(EvalContext& context) const {
    return selected().verifyConstant(context);
}

void MinTypMaxExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("selected", selected());
}

} // namespace slang
