//------------------------------------------------------------------------------
// CallExpression.cpp
// Definitions for call expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/CallExpression.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Constraints.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const InvocationExpressionSyntax& syntax,
                                       const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                       const ASTContext& context) {
    return fromSyntaxImpl(compilation, *syntax.left, &syntax, withClause, context);
}

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const ArrayOrRandomizeMethodExpressionSyntax& syntax,
                                       const ASTContext& context) {
    if (syntax.method->kind == SyntaxKind::InvocationExpression) {
        auto& invoc = syntax.method->as<InvocationExpressionSyntax>();
        return fromSyntax(compilation, invoc, &syntax, context);
    }

    return fromSyntaxImpl(compilation, *syntax.method, nullptr, &syntax, context);
}

Expression& CallExpression::fromSyntaxImpl(Compilation& compilation, const ExpressionSyntax& left,
                                           const InvocationExpressionSyntax* invocation,
                                           const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                           const ASTContext& context) {
    if (left.kind == SyntaxKind::MemberAccessExpression) {
        return MemberAccessExpression::fromSyntax(compilation,
                                                  left.as<MemberAccessExpressionSyntax>(),
                                                  invocation, withClause, context);
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
                                       SourceRange range, const ASTContext& context) {
    if (subroutine.index() == 1) {
        SLANG_ASSERT(!thisClass);
        const SystemCallInfo& info = std::get<1>(subroutine);
        return createSystemCall(compilation, *info.subroutine, nullptr, syntax, withClause, range,
                                context);
    }

    // If this is a non-static class method make sure we're allowed to call it.
    // If we're being called through a class handle (thisClass is non-null) that's fine,
    // otherwise we need to be called by a non-static member within the same class.
    auto sub = std::get<0>(subroutine);
    SLANG_ASSERT(sub->getParentScope());
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
            else if (!parent || inStatic || context.flags.has(ASTFlags::StaticInitializer)) {
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

        SLANG_ASSERT(ss);
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

bool Expression::collectArgs(const ASTContext& context, const ArgumentListSyntax& syntax,
                             SmallVectorBase<const SyntaxNode*>& orderedArgs,
                             NamedArgMap& namedArgs) {
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
                orderedArgs.push_back(arg);
            else
                orderedArgs.push_back(arg->as<OrderedArgumentSyntax>().expr);
        }
    }
    return true;
}

static bool checkOutputArgs(const ASTContext& context, bool hasOutputArgs, SourceRange range) {
    if (context.flags.has(ASTFlags::NonProcedural) && hasOutputArgs) {
        context.addDiag(diag::NonProceduralFuncArg, range);
        return false;
    }

    if (context.flags.has(ASTFlags::EventExpression) && hasOutputArgs) {
        context.addDiag(diag::EventExpressionFuncArg, range);
        return false;
    }

    if (context.flags.has(ASTFlags::AssertionExpr) && hasOutputArgs) {
        context.addDiag(diag::AssertionFuncArg, range);
        return false;
    }

    return true;
}

bool CallExpression::bindArgs(const ArgumentListSyntax* argSyntax,
                              std::span<const FormalArgumentSymbol* const> formalArgs,
                              std::string_view symbolName, SourceRange range,
                              const ASTContext& context,
                              SmallVectorBase<const Expression*>& boundArgs, bool isBuiltInMethod) {
    SmallVector<const SyntaxNode*> orderedArgs;
    NamedArgMap namedArgs;
    if (argSyntax) {
        if (!collectArgs(context, *argSyntax, orderedArgs, namedArgs))
            return false;
    }

    // Helper function to register a driver for default value arguments.
    auto addDefaultDriver = [&](const Expression& expr, const FormalArgumentSymbol& formal) {
        if (isBuiltInMethod)
            return;

        switch (formal.direction) {
            case ArgumentDirection::In:
                // Nothing to do for inputs.
                break;
            case ArgumentDirection::Out:
            case ArgumentDirection::InOut:
                // The default value binding should always use bindLValue() which
                // will always return either an AssignmentExpression or a bad expr.
                SLANG_ASSERT(expr.kind == ExpressionKind::Assignment || expr.bad());
                if (expr.kind == ExpressionKind::Assignment)
                    expr.as<AssignmentExpression>().left().requireLValue(context);
                break;
            case ArgumentDirection::Ref:
                if (!formal.flags.has(VariableFlags::Const))
                    expr.requireLValue(context);
                break;
        }
    };

    bool bad = false;
    uint32_t orderedIndex = 0;
    for (auto formal : formalArgs) {
        const Expression* expr = nullptr;
        if (orderedIndex < orderedArgs.size()) {
            auto arg = orderedArgs[orderedIndex++];
            if (arg->kind == SyntaxKind::EmptyArgument) {
                // Empty arguments are allowed as long as a default is provided.
                expr = formal->getDefaultValue();
                if (!expr)
                    context.addDiag(diag::ArgCannotBeEmpty, arg->sourceRange()) << formal->name;
                else
                    addDefaultDriver(*expr, *formal);
            }
            else if (auto exSyn = context.requireSimpleExpr(arg->as<PropertyExprSyntax>())) {
                expr = &Expression::bindArgument(formal->getType(), formal->direction,
                                                 formal->flags, *exSyn, context);
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
                expr = formal->getDefaultValue();
                if (!expr) {
                    context.addDiag(diag::ArgCannotBeEmpty, it->second.first->sourceRange())
                        << formal->name;
                }
                else {
                    addDefaultDriver(*expr, *formal);
                }
            }
            else if (auto exSyn = context.requireSimpleExpr(*arg)) {
                expr = &Expression::bindArgument(formal->getType(), formal->direction,
                                                 formal->flags, *exSyn, context);
            }
        }
        else {
            expr = formal->getDefaultValue();
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
            else {
                addDefaultDriver(*expr, *formal);
            }
        }

        if (!expr) {
            bad = true;
        }
        else {
            bad |= expr->bad();
            boundArgs.push_back(expr);
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

static void addSubroutineDrivers(const Symbol& procedure, const SubroutineSymbol& sub,
                                 const Expression& callExpr);

Expression& CallExpression::fromArgs(Compilation& compilation, const Subroutine& subroutine,
                                     const Expression* thisClass,
                                     const ArgumentListSyntax* argSyntax, SourceRange range,
                                     const ASTContext& context) {
    SmallVector<const Expression*> boundArgs;
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    bool bad = !bindArgs(argSyntax, symbol.getArguments(), symbol.name, range, context, boundArgs,
                         symbol.flags.has(MethodFlags::BuiltIn));

    auto result = compilation.emplace<CallExpression>(&symbol, symbol.getReturnType(), thisClass,
                                                      boundArgs.copy(compilation),
                                                      context.getLocation(), range);
    if (bad)
        return badExpr(compilation, result);

    if (context.flags.has(ASTFlags::Function | ASTFlags::Final) &&
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

    // If this subroutine is invoked from a procedure, register drivers for this
    // particular procedure to detect multiple driver violations.
    if (!thisClass && symbol.subroutineKind == SubroutineKind::Function) {
        if (auto proc = context.getProceduralBlock(); proc && !context.scope->isUninstantiated())
            addSubroutineDrivers(*proc, symbol, *result);
    }

    return *result;
}

Expression& CallExpression::fromSystemMethod(
    Compilation& compilation, const Expression& expr, const LookupResult::MemberSelector& selector,
    const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const ASTContext& context) {

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
    std::string_view methodName, const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const ASTContext& context) {

    auto subroutine = compilation.getSystemMethod(rootKind, methodName);
    if (!subroutine)
        return nullptr;

    return &createSystemCall(compilation, *subroutine, &expr, syntax, withClause,
                             syntax ? syntax->sourceRange() : expr.sourceRange, context);
}

static bool getIteratorParams(std::string_view subroutineName, const ArgumentListSyntax& arguments,
                              const ASTContext& context, std::string_view& iteratorName,
                              std::string_view& indexMethodName, SourceLocation& iteratorLoc) {
    auto actualArgs = arguments.parameters;
    if (actualArgs.empty())
        return true;

    if (actualArgs.size() > 2) {
        auto& diag = context.addDiag(diag::TooManyArguments, arguments.sourceRange());
        diag << subroutineName;
        diag << 2;
        diag << actualArgs.size();
        return false;
    }

    auto getId = [&](const ArgumentSyntax& argSyntax) -> Token {
        switch (argSyntax.kind) {
            case SyntaxKind::OrderedArgument: {
                auto exSyn = context.requireSimpleExpr(*argSyntax.as<OrderedArgumentSyntax>().expr);
                if (!exSyn)
                    return Token();

                if (exSyn->kind != SyntaxKind::IdentifierName) {
                    context.addDiag(diag::ExpectedIteratorName, exSyn->sourceRange());
                    return Token();
                }

                return exSyn->as<IdentifierNameSyntax>().identifier;
            }
            case SyntaxKind::NamedArgument:
                context.addDiag(diag::NamedArgNotAllowed, argSyntax.sourceRange());
                return Token();
            case SyntaxKind::EmptyArgument:
                context.addDiag(diag::EmptyArgNotAllowed, argSyntax.sourceRange());
                return Token();
            default:
                SLANG_UNREACHABLE;
        }
    };

    auto iteratorTok = getId(*actualArgs[0]);
    if (!iteratorTok || iteratorTok.isMissing())
        return false;

    if (actualArgs.size() > 1) {
        auto indexTok = getId(*actualArgs[1]);
        if (!indexTok || indexTok.isMissing())
            return false;

        indexMethodName = indexTok.valueText();

        auto languageVersion = context.getCompilation().languageVersion();
        if (languageVersion < LanguageVersion::v1800_2023) {
            context.addDiag(diag::WrongLanguageVersion, actualArgs[1]->sourceRange())
                << toString(languageVersion);
        }
    }

    iteratorName = iteratorTok.valueText();
    iteratorLoc = iteratorTok.location();

    return true;
}

static const Expression* bindIteratorExpr(Compilation& compilation, std::string_view subroutineName,
                                          const InvocationExpressionSyntax* invocation,
                                          const ArrayOrRandomizeMethodExpressionSyntax& withClause,
                                          const Type& arrayType, const ASTContext& context,
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

    // If arguments are provided, there can be one or two.
    // The first is the name of iterator, and the second is the name
    // of the index method on that iterator. Otherwise we use defaults
    // for those names.
    SourceLocation iteratorLoc = SourceLocation::NoLocation;
    std::string_view iteratorName = "item"sv;
    std::string_view indexMethodName = "index"sv;
    if (invocation && invocation->arguments) {
        if (!getIteratorParams(subroutineName, *invocation->arguments, context, iteratorName,
                               indexMethodName, iteratorLoc)) {
            return nullptr;
        }
    }

    // Create the iterator variable and set it up with an AST context so that it
    // can be found by the iteration expression.
    auto it = compilation.emplace<IteratorSymbol>(*context.scope, iteratorName, iteratorLoc,
                                                  arrayType, indexMethodName);
    iterVar = it;

    ASTContext iterCtx = context;
    it->nextTemp = std::exchange(iterCtx.firstTempVar, it);
    iterCtx.flags &= ~ASTFlags::StaticInitializer;

    return &Expression::bind(*withClause.args->expressions[0], iterCtx);
}

Expression& CallExpression::createSystemCall(
    Compilation& compilation, const SystemSubroutine& subroutine, const Expression* firstArg,
    const InvocationExpressionSyntax* syntax,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, SourceRange range,
    const ASTContext& context, const Scope* randomizeScope) {

    SystemCallInfo callInfo{&subroutine, context.scope, {}};
    SmallVector<const Expression*> buffer;
    if (firstArg)
        buffer.push_back(firstArg);

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
            iterOrThis = bindIteratorExpr(compilation, subroutine.name, syntax, *withClause,
                                          *firstArg->type, context, iterVar);
            if (!iterOrThis || iterOrThis->bad())
                return badExpr(compilation, iterOrThis);

            callInfo.extraInfo = IteratorCallInfo{iterOrThis, iterVar};
        }
    }
    else {
        ASTContext::RandomizeDetails randomizeDetails;
        ASTContext argContext = context.resetFlags({});

        if (subroutine.withClauseMode == WithClauseMode::Randomize) {
            // If this is a class-scoped randomize call, setup the scope properly
            // so that class members can be found in the constraint block.
            argContext.randomizeDetails = &randomizeDetails;
            if (firstArg) {
                randomizeDetails.classType = &firstArg->type->getCanonicalType().as<ClassType>();
                randomizeDetails.thisVar = firstArg->getSymbolReference();
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

                    SmallVector<std::string_view> names;
                    for (auto expr : withClause->args->expressions) {
                        if (expr->kind != SyntaxKind::IdentifierName) {
                            argContext.addDiag(diag::ExpectedIdentifier, expr->sourceRange());
                            continue;
                        }

                        names.push_back(expr->as<IdentifierNameSyntax>().identifier.valueText());
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
                                buffer.push_back(&ClockingEventExpression::fromSyntax(
                                    arg.expr->as<ClockingPropertyExprSyntax>(), argContext));
                            }
                            else {
                                argContext.addDiag(diag::TimingControlNotAllowed,
                                                   actualArgs[i]->sourceRange());
                                return badExpr(compilation, nullptr);
                            }
                        }
                        else if (auto exSyn = context.requireSimpleExpr(*arg.expr)) {
                            buffer.push_back(
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
                            buffer.push_back(compilation.emplace<EmptyArgumentExpression>(
                                compilation.getVoidType(), actualArgs[i]->sourceRange()));
                        }
                        else {
                            argContext.addDiag(diag::EmptyArgNotAllowed,
                                               actualArgs[i]->sourceRange());
                            return badExpr(compilation, nullptr);
                        }
                        break;
                    default:
                        SLANG_UNREACHABLE;
                }
            }
        }

        if (withClause) {
            // Finally bind the inline constraint block if we have one.
            SLANG_ASSERT(withClause->constraints);

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
    auto expr = compilation.emplace<CallExpression>(callInfo, type, nullptr,
                                                    buffer.copy(compilation), context.getLocation(),
                                                    range);

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
    // If thisClass() is set call eval on it to be sure an error is issued.
    if (thisClass()) {
        auto cv = thisClass()->eval(context);
        SLANG_ASSERT(!cv);
        return nullptr;
    }

    // Delegate system calls to their appropriate handler.
    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->eval(context, arguments(), sourceRange, callInfo);
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!checkConstant(context, symbol, sourceRange))
        return nullptr;

    // Evaluate all argument in the current stack frame.
    SmallVector<ConstantValue, 4> args;
    for (auto arg : arguments()) {
        ConstantValue v = arg->eval(context);
        if (!v)
            return nullptr;
        args.emplace_back(std::move(v));
    }

    // Push a new stack frame, push argument values as locals.
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return nullptr;

    std::span<const FormalArgumentSymbol* const> formals = symbol.getArguments();
    for (size_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    SLANG_ASSERT(symbol.returnValVar);
    context.createLocal(symbol.returnValVar);

    using ER = Statement::EvalResult;
    ER er = symbol.getBody().eval(context);

    // If we got a disable result, it means a disable statement was evaluated that
    // targeted a block that wasn't executing. This isn't allowed in a constant expression.
    // Handle this before popping the frame so that we get the stack reported.
    if (er == ER::Disable)
        context.addDiag(diag::ConstEvalDisableTarget, context.getDisableRange());

    ConstantValue result = std::move(*context.findLocal(symbol.returnValVar));
    context.popFrame();

    if (er == ER::Fail || er == ER::Disable)
        return nullptr;

    SLANG_ASSERT(er == ER::Success || er == ER::Return);
    return result;
}

std::optional<bitwidth_t> CallExpression::getEffectiveWidthImpl() const {
    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        if (auto result = callInfo.subroutine->getEffectiveWidth())
            return result;
    }
    return type->getBitWidth();
}

Expression::EffectiveSign CallExpression::getEffectiveSignImpl(bool) const {
    if (isSystemCall()) {
        auto& callInfo = std::get<1>(subroutine);
        if (callInfo.subroutine->getEffectiveWidth() == 1)
            return EffectiveSign::Either;
    }
    return type->isSigned() ? EffectiveSign::Signed : EffectiveSign::Unsigned;
}

bool CallExpression::checkConstant(EvalContext& context, const SubroutineSymbol& subroutine,
                                   SourceRange range) {
    if (context.flags.has(EvalFlags::IsScript))
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

    if (subroutine.flags.has(MethodFlags::BuiltIn | MethodFlags::InterfaceExtern |
                             MethodFlags::ModportExport | MethodFlags::ModportImport)) {
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
    SLANG_ASSERT(scope);
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
        return {nullptr, nullptr};
    return {itInfo->iterExpr, itInfo->iterVar};
}

std::string_view CallExpression::getSubroutineName() const {
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

bool CallExpression::hasOutputArgs() const {
    if (subroutine.index() == 1) {
        auto& callInfo = std::get<1>(subroutine);
        return callInfo.subroutine->hasOutputArgs;
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    return symbol.hasOutputArgs();
}

void CallExpression::serializeTo(ASTSerializer& serializer) const {
    if (subroutine.index() == 1) {
        auto& callInfo = std::get<1>(subroutine);
        serializer.write("subroutine", callInfo.subroutine->name);

        if (callInfo.extraInfo.index() == 1) {
            auto& itInfo = std::get<1>(callInfo.extraInfo);
            if (itInfo.iterVar)
                serializer.write("iterVar", *itInfo.iterVar);
            if (itInfo.iterExpr)
                serializer.write("iterExpr", *itInfo.iterExpr);
        }
        else if (callInfo.extraInfo.index() == 2) {
            auto& randInfo = std::get<2>(callInfo.extraInfo);
            if (randInfo.inlineConstraints)
                serializer.write("inlineConstraints", *randInfo.inlineConstraints);

            if (!randInfo.constraintRestrictions.empty()) {
                serializer.startArray("constraintRestrictions");
                for (auto name : randInfo.constraintRestrictions)
                    serializer.serialize(name);
                serializer.endArray();
            }
        }
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

class DriverVisitor : public ASTVisitor<DriverVisitor, true, true> {
public:
    const Symbol& procedure;
    const SubroutineSymbol& sub;
    const Expression& callExpr;
    SmallSet<const ValueSymbol*, 8> visitedValues;
    SmallSet<const SubroutineSymbol*, 4>& visitedSubs;

    DriverVisitor(const Symbol& procedure, SmallSet<const SubroutineSymbol*, 4>& visitedSubs,
                  const SubroutineSymbol& sub, const Expression& callExpr) :
        procedure(procedure), sub(sub), callExpr(callExpr), visitedSubs(visitedSubs) {}

    void handle(const CallExpression& expr) {
        if (!expr.isSystemCall() && !expr.thisClass()) {
            auto& subroutine = *std::get<0>(expr.subroutine);
            if (subroutine.subroutineKind == SubroutineKind::Function &&
                visitedSubs.emplace(&subroutine).second) {

                DriverVisitor visitor(procedure, visitedSubs, subroutine, callExpr);
                subroutine.getBody().visit(visitor);
            }
        }
    }

    void handle(const ValueExpressionBase& expr) {
        auto& sym = expr.symbol;
        if (!visitedValues.emplace(&sym).second)
            return;

        if (sub.getCompilation().hasFlag(CompilationFlags::AllowMultiDrivenLocals)) {
            auto scope = sym.getParentScope();
            while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock)
                scope = scope->asSymbol().getParentScope();

            if (scope == &sub) {
                // This is a local variable of the subroutine,
                // so don't do driver checking.
                return;
            }
        }

        // If the target symbol is driven by the subroutine we're inspecting,
        // add another driver for the procedure we're originally called from.
        SmallVector<std::pair<DriverBitRange, const ValueDriver*>> drivers;
        auto range = sym.drivers();
        for (auto it = range.begin(); it != range.end(); ++it) {
            if ((*it)->containingSymbol == &sub)
                drivers.push_back({it.bounds(), *it});
        }

        // This needs to be a separate loop to avoid mutating the driver map
        // while iterating over it.
        for (auto [bounds, driver] : drivers) {
            sym.addDriver(DriverKind::Procedural, bounds, *driver->prefixExpression, procedure,
                          callExpr);
        }
    }
};

static void addSubroutineDrivers(const Symbol& procedure, const SubroutineSymbol& sub,
                                 const Expression& callExpr) {
    SmallSet<const SubroutineSymbol*, 4> visitedSubs;
    visitedSubs.emplace(&sub);

    DriverVisitor visitor(procedure, visitedSubs, sub, callExpr);
    sub.getBody().visit(visitor);
}

} // namespace slang::ast
