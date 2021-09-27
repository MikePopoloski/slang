//------------------------------------------------------------------------------
// CallExpression.cpp
// Definitions for call expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/CallExpression.h"

#include "slang/binding/Constraints.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/SelectExpressions.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const InvocationExpressionSyntax& syntax,
                                       const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                       const BindContext& context) {
    return fromSyntaxImpl(compilation, *syntax.left, &syntax, withClause, context);
}

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const ArrayOrRandomizeMethodExpressionSyntax& syntax,
                                       const BindContext& context) {
    if (syntax.method->kind == SyntaxKind::InvocationExpression) {
        auto& invoc = syntax.method->as<InvocationExpressionSyntax>();
        return fromSyntax(compilation, invoc, &syntax, context);
    }

    return fromSyntaxImpl(compilation, *syntax.method, nullptr, &syntax, context);
}

Expression& CallExpression::fromSyntaxImpl(Compilation& compilation, const ExpressionSyntax& left,
                                           const InvocationExpressionSyntax* invocation,
                                           const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                           const BindContext& context) {
    if (left.kind == SyntaxKind::MemberAccessExpression) {
        return MemberAccessExpression::fromSyntax(
            compilation, left.as<MemberAccessExpressionSyntax>(), invocation, withClause, context);
    }

    if (!NameSyntax::isKind(left.kind)) {
        SourceLocation loc = (invocation && invocation->arguments)
                                 ? invocation->arguments->openParen.location()
                                 : left.getFirstToken().location();
        auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
        diag << left.sourceRange();
        return badExpr(compilation, nullptr);
    }

    return bindName(compilation, left.as<NameSyntax>(), invocation, withClause, context);
}

Expression& CallExpression::fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                       const Expression* thisClass,
                                       const InvocationExpressionSyntax* syntax,
                                       const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                       SourceRange range, const BindContext& context) {
    if (subroutine.index() == 1) {
        ASSERT(!thisClass);
        const SystemCallInfo& info = std::get<1>(subroutine);
        return createSystemCall(compilation, *info.subroutine, nullptr, syntax, withClause, range,
                                context);
    }

    // If this is a non-static class method make sure we're allowed to call it.
    // If we're being called through a class handle (thisClass is non-null) that's fine,
    // otherwise we need to be called by a non-static member within the same class.
    auto sub = std::get<0>(subroutine);
    ASSERT(sub->getParentScope());
    auto& subroutineParent = sub->getParentScope()->asSymbol();
    if (!sub->flags.has(MethodFlags::Static) && !thisClass &&
        subroutineParent.kind == SymbolKind::ClassType) {

        if (!context.randomizeDetails || !context.randomizeDetails->classType ||
            !Lookup::isAccessibleFrom(*sub, context.randomizeDetails->classType->asSymbol())) {

            auto [parent, inStatic] = Lookup::getContainingClass(*context.scope);
            if (parent && !Lookup::isAccessibleFrom(*sub, *parent)) {
                auto& diag = context.addDiag(diag::NestedNonStaticClassMethod, range);
                diag << parent->name;
                return badExpr(compilation, nullptr);
            }
            else if (!parent || inStatic || (context.flags & BindFlags::StaticInitializer) != 0) {
                context.addDiag(diag::NonStaticClassMethod, range);
                return badExpr(compilation, nullptr);
            }
        }
    }

    // The built-in randomize method is found via normal lookup but it has special syntax rules,
    // so translate that into a call to a system subroutine that can handle those rules.
    if (sub->flags.has(MethodFlags::Randomize)) {
        // If the parent is a class, look up the special randomize method on ClassTypes.
        // Otherwise, this is the free std::randomize function.
        const SystemSubroutine* ss;
        if (subroutineParent.kind == SymbolKind::ClassType)
            ss = compilation.getSystemMethod(SymbolKind::ClassType, sub->name);
        else
            ss = compilation.getSystemSubroutine(sub->name);

        ASSERT(ss);
        return createSystemCall(compilation, *ss, thisClass, syntax, withClause, range, context,
                                sub->getParentScope());
    }

    if (withClause) {
        context.addDiag(diag::WithClauseNotAllowed, withClause->with.range()) << sub->name;
        return badExpr(compilation, nullptr);
    }

    // Can only omit the parentheses for invocation if the subroutine is a task,
    // void function, or class method.
    if (!syntax && subroutineParent.kind != SymbolKind::ClassType) {
        if (!sub->getReturnType().isVoid()) {
            context.addDiag(diag::MissingInvocationParens, range) << sub->name;
            return badExpr(compilation, nullptr);
        }
    }

    auto& result = fromArgs(compilation, subroutine, thisClass,
                            syntax ? syntax->arguments : nullptr, range, context);
    if (syntax)
        context.setAttributes(result, syntax->attributes);

    return result;
}

bool Expression::collectArgs(const BindContext& context, const ArgumentListSyntax& syntax,
                             SmallVector<const SyntaxNode*>& orderedArgs, NamedArgMap& namedArgs) {
    // Collect all arguments into a list of ordered expressions (which can
    // optionally be nullptr to indicate an empty argument) and a map of
    // named argument assignments.
    for (auto arg : syntax.parameters) {
        if (arg->kind == SyntaxKind::NamedArgument) {
            const NamedArgumentSyntax& nas = arg->as<NamedArgumentSyntax>();
            auto name = nas.name.valueText();
            if (!name.empty()) {
                auto pair = namedArgs.emplace(name, std::make_pair(&nas, false));
                if (!pair.second) {
                    auto& diag = context.addDiag(diag::DuplicateArgAssignment, nas.name.location());
                    diag << name;
                    diag.addNote(diag::NotePreviousUsage,
                                 pair.first->second.first->name.location());
                }
            }
        }
        else {
            // Once a named argument has been seen, no more ordered arguments are allowed.
            if (!namedArgs.empty()) {
                context.addDiag(diag::MixingOrderedAndNamedArgs, arg->getFirstToken().location());
                return false;
            }

            if (arg->kind == SyntaxKind::EmptyArgument)
                orderedArgs.append(arg);
            else
                orderedArgs.append(arg->as<OrderedArgumentSyntax>().expr);
        }
    }
    return true;
}

static bool checkOutputArgs(const BindContext& context, bool hasOutputArgs, SourceRange range) {
    if (context.flags.has(BindFlags::NonProcedural) && hasOutputArgs) {
        context.addDiag(diag::NonProceduralFuncArg, range);
        return false;
    }

    if (context.flags.has(BindFlags::EventExpression) && hasOutputArgs) {
        context.addDiag(diag::EventExpressionFuncArg, range);
        return false;
    }

    if (context.flags.has(BindFlags::AssertionExpr) && hasOutputArgs) {
        context.addDiag(diag::AssertionFuncArg, range);
        return false;
    }

    return true;
}

bool CallExpression::bindArgs(const ArgumentListSyntax* argSyntax,
                              span<const FormalArgumentSymbol* const> formalArgs,
                              string_view symbolName, SourceRange range, const BindContext& context,
                              SmallVector<const Expression*>& boundArgs) {
    SmallVectorSized<const SyntaxNode*, 8> orderedArgs;
    NamedArgMap namedArgs;
    if (argSyntax) {
        if (!collectArgs(context, *argSyntax, orderedArgs, namedArgs))
            return false;
    }

    bool bad = false;
    uint32_t orderedIndex = 0;
    for (auto formal : formalArgs) {
        const Expression* expr = nullptr;
        if (orderedIndex < orderedArgs.size()) {
            auto arg = orderedArgs[orderedIndex++];
            if (arg->kind == SyntaxKind::EmptyArgument) {
                // Empty arguments are allowed as long as a default is provided.
                expr = formal->getInitializer();
                if (!expr)
                    context.addDiag(diag::ArgCannotBeEmpty, arg->sourceRange()) << formal->name;
            }
            else if (auto exSyn = context.requireSimpleExpr(arg->as<PropertyExprSyntax>())) {
                expr = &Expression::bindArgument(formal->getType(), formal->direction, *exSyn,
                                                 context, formal->isConstant);
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
            else if (auto exSyn = context.requireSimpleExpr(*arg)) {
                expr = &Expression::bindArgument(formal->getType(), formal->direction, *exSyn,
                                                 context, formal->isConstant);
            }
        }
        else {
            expr = formal->getInitializer();
            if (!expr) {
                if (namedArgs.empty()) {
                    auto& diag = context.addDiag(diag::TooFewArguments, range);
                    diag << symbolName;
                    diag << formalArgs.size() << orderedArgs.size();
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
        diag << symbolName;
        diag << formalArgs.size();
        diag << orderedArgs.size();
        bad = true;
    }

    for (const auto& pair : namedArgs) {
        // We marked all the args that we used, so anything left over is an arg assignment
        // for a non-existent arg.
        if (!pair.second.second) {
            auto& diag = context.addDiag(diag::ArgDoesNotExist, pair.second.first->name.location());
            diag << pair.second.first->name.valueText();
            diag << symbolName;
            bad = true;
        }
    }

    return !bad;
}

Expression& CallExpression::fromArgs(Compilation& compilation, const Subroutine& subroutine,
                                     const Expression* thisClass,
                                     const ArgumentListSyntax* argSyntax, SourceRange range,
                                     const BindContext& context) {
    SmallVectorSized<const Expression*, 8> boundArgs;
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    bool bad = !bindArgs(argSyntax, symbol.getArguments(), symbol.name, range, context, boundArgs);

    auto result = compilation.emplace<CallExpression>(&symbol, symbol.getReturnType(), thisClass,
                                                      boundArgs.copy(compilation),
                                                      context.getLocation(), range);
    if (bad)
        return badExpr(compilation, result);

    if (context.flags.has(BindFlags::Function | BindFlags::Final) &&
        symbol.subroutineKind == SubroutineKind::Task) {
        const Scope* scope = context.scope;
        while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock)
            scope = scope->asSymbol().getParentScope();

        if (scope && scope->asSymbol().kind == SymbolKind::Subroutine)
            context.addDiag(diag::TaskFromFunction, range);
        else
            context.addDiag(diag::TaskFromFinal, range);

        return badExpr(compilation, result);
    }

    if (!checkOutputArgs(context, symbol.hasOutputArgs(), range))
        return badExpr(compilation, result);

    return *result;
}

Expression& CallExpression::fromSystemMethod(
    Compilation& compilation, const Expression& expr, const LookupResult::MemberSelector& selector,
    const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const BindContext& context) {

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

    return createSystemCall(compilation, *subroutine, &expr, syntax, withClause,
                            syntax ? syntax->sourceRange() : expr.sourceRange, context);
}

Expression* CallExpression::fromBuiltInMethod(
    Compilation& compilation, SymbolKind rootKind, const Expression& expr,
    const LookupResult::MemberSelector& selector, const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const BindContext& context) {

    auto subroutine = compilation.getSystemMethod(rootKind, selector.name);
    if (!subroutine)
        return nullptr;

    return &createSystemCall(compilation, *subroutine, &expr, syntax, withClause,
                             syntax ? syntax->sourceRange() : expr.sourceRange, context);
}

static const Expression* bindIteratorExpr(Compilation& compilation,
                                          const InvocationExpressionSyntax* invocation,
                                          const ArrayOrRandomizeMethodExpressionSyntax& withClause,
                                          const Type& arrayType, const BindContext& context,
                                          const ValueSymbol*& iterVar) {
    // Can't be a constraint block here.
    if (withClause.constraints) {
        context.addDiag(diag::UnexpectedConstraintBlock, withClause.constraints->sourceRange());
        return nullptr;
    }

    if (!withClause.args) {
        context.addDiag(diag::ExpectedIterationExpression, withClause.with.range());
        return nullptr;
    }

    if (withClause.args->expressions.size() != 1) {
        context.addDiag(diag::ExpectedIterationExpression, withClause.args->sourceRange());
        return nullptr;
    }

    // If arguments are provided, there should be only one and it should
    // be the name of the iterator symbol. Otherwise, we need to automatically
    // generate an iterator symbol named 'item'.
    SourceLocation iteratorLoc = SourceLocation::NoLocation;
    string_view iteratorName;
    if (invocation && invocation->arguments) {
        auto actualArgs = invocation->arguments->parameters;
        if (actualArgs.size() == 1 && actualArgs[0]->kind == SyntaxKind::OrderedArgument) {
            auto& arg = actualArgs[0]->as<OrderedArgumentSyntax>();
            if (auto exSyn = context.requireSimpleExpr(*arg.expr)) {
                if (exSyn->kind == SyntaxKind::IdentifierName) {
                    auto id = exSyn->as<IdentifierNameSyntax>().identifier;
                    iteratorLoc = id.location();
                    iteratorName = id.valueText();
                    if (iteratorName.empty())
                        return nullptr;
                }
            }
            else {
                return nullptr;
            }
        }

        if (iteratorName.empty() && !actualArgs.empty()) {
            context.addDiag(diag::ExpectedIteratorName, invocation->arguments->sourceRange());
            return nullptr;
        }
    }

    if (iteratorName.empty())
        iteratorName = "item"sv;

    // Create the iterator variable and set it up with a bind context so that it
    // can be found by the iteration expression.
    auto it =
        compilation.emplace<IteratorSymbol>(*context.scope, iteratorName, iteratorLoc, arrayType);
    iterVar = it;

    BindContext iterCtx = context;
    it->nextIterator = std::exchange(iterCtx.firstIterator, it);
    iterCtx.flags &= ~BindFlags::StaticInitializer;

    return &Expression::bind(*withClause.args->expressions[0], iterCtx);
}

Expression& CallExpression::createSystemCall(
    Compilation& compilation, const SystemSubroutine& subroutine, const Expression* firstArg,
    const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, SourceRange range,
    const BindContext& context, const Scope* randomizeScope) {

    SystemCallInfo callInfo{ &subroutine, context.scope, {} };
    SmallVectorSized<const Expression*, 8> buffer;
    if (firstArg)
        buffer.append(firstArg);

    const Expression* iterOrThis = nullptr;
    const ValueSymbol* iterVar = nullptr;
    using WithClauseMode = SystemSubroutine::WithClauseMode;
    if (subroutine.withClauseMode == WithClauseMode::Iterator) {
        // 'with' clause is not required. If it's not there, no arguments
        // can be provided.
        if (!withClause) {
            if (syntax && syntax->arguments && !syntax->arguments->parameters.empty()) {
                context.addDiag(diag::IteratorArgsWithoutWithClause,
                                syntax->arguments->sourceRange())
                    << subroutine.name;
                return badExpr(compilation, nullptr);
            }
        }
        else if (firstArg) {
            iterOrThis = bindIteratorExpr(compilation, syntax, *withClause, *firstArg->type,
                                          context, iterVar);
            if (!iterOrThis || iterOrThis->bad())
                return badExpr(compilation, iterOrThis);

            callInfo.extraInfo = IteratorCallInfo{ iterOrThis, iterVar };
        }
    }
    else {
        BindContext::RandomizeDetails randomizeDetails;
        BindContext argContext = context;

        if (subroutine.withClauseMode == WithClauseMode::Randomize) {
            // If this is a class-scoped randomize call, setup the scope properly
            // so that class members can be found in the constraint block.
            argContext.randomizeDetails = &randomizeDetails;
            if (firstArg) {
                randomizeDetails.classType = &firstArg->type->getCanonicalType().as<ClassType>();
            }
            else if (randomizeScope && randomizeScope->asSymbol().kind == SymbolKind::ClassType) {
                randomizeDetails.classType = randomizeScope;
            }
            iterOrThis = firstArg;
        }

        if (withClause) {
            if (subroutine.withClauseMode == WithClauseMode::Randomize) {
                if (!withClause->constraints) {
                    argContext.addDiag(diag::MissingConstraintBlock, withClause->sourceRange());
                    return badExpr(compilation, nullptr);
                }

                RandomizeCallInfo randInfo;
                if (withClause->args) {
                    if (!argContext.randomizeDetails || !argContext.randomizeDetails->classType) {
                        argContext.addDiag(diag::NameListWithScopeRandomize,
                                           withClause->args->sourceRange());
                        return badExpr(compilation, nullptr);
                    }

                    SmallVectorSized<string_view, 4> names;
                    for (auto expr : withClause->args->expressions) {
                        if (expr->kind != SyntaxKind::IdentifierName) {
                            argContext.addDiag(diag::ExpectedIdentifier, expr->sourceRange());
                            continue;
                        }

                        names.append(expr->as<IdentifierNameSyntax>().identifier.valueText());
                    }

                    randInfo.constraintRestrictions = names.copy(argContext.getCompilation());
                }

                callInfo.extraInfo = randInfo;
            }
            else {
                argContext.addDiag(diag::WithClauseNotAllowed, withClause->with.range())
                    << subroutine.name;
                return badExpr(compilation, nullptr);
            }
        }

        // Bind arguments as we would for any ordinary method.
        if (syntax && syntax->arguments) {
            auto actualArgs = syntax->arguments->parameters;
            for (size_t i = 0; i < actualArgs.size(); i++) {
                size_t index = i + (firstArg ? 1 : 0);
                switch (actualArgs[i]->kind) {
                    case SyntaxKind::OrderedArgument: {
                        const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
                        if (arg.expr->kind == SyntaxKind::ClockingPropertyExpr) {
                            if (subroutine.allowClockingArgument(index)) {
                                buffer.append(&ClockingEventExpression::fromSyntax(
                                    arg.expr->as<ClockingPropertyExprSyntax>(), argContext));
                            }
                            else {
                                argContext.addDiag(diag::TimingControlNotAllowed,
                                                   actualArgs[i]->sourceRange());
                                return badExpr(compilation, nullptr);
                            }
                        }
                        else if (auto exSyn = context.requireSimpleExpr(*arg.expr)) {
                            buffer.append(
                                &subroutine.bindArgument(index, argContext, *exSyn, buffer));
                        }
                        else {
                            return badExpr(compilation, nullptr);
                        }
                        break;
                    }
                    case SyntaxKind::NamedArgument:
                        argContext.addDiag(diag::NamedArgNotAllowed, actualArgs[i]->sourceRange());
                        return badExpr(compilation, nullptr);
                    case SyntaxKind::EmptyArgument:
                        if (subroutine.allowEmptyArgument(index)) {
                            buffer.append(compilation.emplace<EmptyArgumentExpression>(
                                compilation.getVoidType(), actualArgs[i]->sourceRange()));
                        }
                        else {
                            argContext.addDiag(diag::EmptyArgNotAllowed,
                                               actualArgs[i]->sourceRange());
                            return badExpr(compilation, nullptr);
                        }
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
        }

        if (withClause) {
            // Finally bind the inline constraint block if we have one.
            ASSERT(withClause->constraints);

            // For scope randomize calls we need to register the
            // arg variables so they get treated as 'rand'.
            if (!randomizeDetails.classType) {
                for (auto arg : buffer) {
                    auto sym = arg->getSymbolReference();
                    if (sym)
                        randomizeDetails.scopeRandVars.emplace(sym);
                }
            }

            auto& randInfo = std::get<2>(callInfo.extraInfo);
            randomizeDetails.nameRestrictions = randInfo.constraintRestrictions;
            randInfo.inlineConstraints = &Constraint::bind(*withClause->constraints, argContext);
        }
    }

    const Type& type = subroutine.checkArguments(context, buffer, range, iterOrThis);
    auto expr = compilation.emplace<CallExpression>(
        callInfo, type, nullptr, buffer.copy(compilation), context.getLocation(), range);

    if (type.isError())
        return badExpr(compilation, expr);

    for (auto arg : expr->arguments()) {
        if (arg->bad())
            return badExpr(compilation, expr);
    }

    if (!checkOutputArgs(context, subroutine.hasOutputArgs, range))
        return badExpr(compilation, expr);

    if (syntax)
        context.setAttributes(*expr, syntax->attributes);

    return *expr;
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Delegate system calls to their appropriate handler.
    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->eval(context, arguments(), callInfo);
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!checkConstant(context, symbol, sourceRange))
        return nullptr;

    // If thisClass() is set, we will already have issued an error when
    // verifying constant-ness. Just fail silently here.
    if (thisClass())
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

    span<const FormalArgumentSymbol* const> formals = symbol.getArguments();
    for (size_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    ASSERT(symbol.returnValVar);
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
    if (thisClass() && !thisClass()->verifyConstant(context))
        return false;

    for (auto arg : arguments()) {
        if (!arg->verifyConstant(context))
            return false;
    }

    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        auto iteratorInfo = std::get_if<IteratorCallInfo>(&callInfo.extraInfo);

        if (iteratorInfo && iteratorInfo->iterExpr &&
            !iteratorInfo->iterExpr->verifyConstant(context)) {
            return false;
        }

        return callInfo.subroutine->verifyConstant(context, arguments(), sourceRange);
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!checkConstant(context, symbol, sourceRange))
        return false;

    // Recursive function calls check body only once
    // otherwise never finish until exceeding depth limit.
    if (inRecursion)
        return true;

    inRecursion = true;
    auto guard = ScopeGuard([this] { inRecursion = false; });

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

    if (subroutine.flags.has(MethodFlags::DPIImport)) {
        context.addDiag(diag::ConstEvalDPINotConstant, range);
        return false;
    }

    if (subroutine.flags.has(MethodFlags::Virtual | MethodFlags::Pure | MethodFlags::Constructor)) {
        context.addDiag(diag::ConstEvalMethodNotConstant, range);
        return false;
    }

    if (subroutine.flags.has(MethodFlags::NotConst)) {
        context.addDiag(diag::ConstEvalSubroutineNotConstant, range) << subroutine.name;
        return false;
    }

    if (subroutine.getReturnType().isVoid()) {
        context.addDiag(diag::ConstEvalVoidNotConstant, range);
        return false;
    }

    for (auto arg : subroutine.getArguments()) {
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

std::pair<const Expression*, const ValueSymbol*> CallExpression::SystemCallInfo::getIteratorInfo()
    const {
    auto itInfo = std::get_if<IteratorCallInfo>(&extraInfo);
    if (!itInfo)
        return { nullptr, nullptr };
    return { itInfo->iterExpr, itInfo->iterVar };
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

    if (thisClass())
        serializer.write("thisClass", *thisClass());

    if (!arguments().empty()) {
        serializer.startArray("arguments");
        for (auto arg : arguments())
            serializer.serialize(*arg);
        serializer.endArray();
    }
}

} // namespace slang
