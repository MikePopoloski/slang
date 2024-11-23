//------------------------------------------------------------------------------
// LoopStatements.cpp
// Loop statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/statements/LoopStatements.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

using ER = Statement::EvalResult;

Statement& ReturnStatement::fromSyntax(Compilation& compilation,
                                       const ReturnStatementSyntax& syntax,
                                       const ASTContext& context, StatementContext& stmtCtx) {
    if (stmtCtx.flags.has(StatementFlags::InForkJoin)) {
        context.addDiag(diag::ReturnInParallel, syntax.sourceRange());
        return badStmt(compilation, nullptr);
    }

    // Find the parent subroutine or randsequence production.
    const Scope* scope = context.scope;
    while (scope->asSymbol().kind == SymbolKind::StatementBlock)
        scope = scope->asSymbol().getParentScope();

    auto stmtRange = syntax.returnKeyword.range();
    auto& symbol = scope->asSymbol();
    if (symbol.kind != SymbolKind::Subroutine && symbol.kind != SymbolKind::RandSeqProduction) {
        context.addDiag(diag::ReturnNotInSubroutine, stmtRange);
        return badStmt(compilation, nullptr);
    }

    auto& returnType = symbol.getDeclaredType()->getType();
    const Expression* retExpr = nullptr;
    if (syntax.returnValue) {
        retExpr = &Expression::bindRValue(returnType, *syntax.returnValue, stmtRange, context);
    }
    else if (!returnType.isVoid()) {
        DiagCode code = symbol.kind == SymbolKind::Subroutine ? diag::MissingReturnValue
                                                              : diag::MissingReturnValueProd;
        context.addDiag(code, syntax.sourceRange());
        return badStmt(compilation, nullptr);
    }

    auto result = compilation.emplace<ReturnStatement>(retExpr, syntax.sourceRange());
    if (retExpr && retExpr->bad())
        return badStmt(compilation, result);

    return *result;
}

ER ReturnStatement::evalImpl(EvalContext& context) const {
    if (expr) {
        const SubroutineSymbol* subroutine = context.topFrame().subroutine;
        SLANG_ASSERT(subroutine);

        ConstantValue* storage = context.findLocal(subroutine->returnValVar);
        SLANG_ASSERT(storage);

        *storage = expr->eval(context);
    }
    return ER::Return;
}

void ReturnStatement::serializeTo(ASTSerializer& serializer) const {
    if (expr)
        serializer.write("expr", *expr);
}

Statement& BreakStatement::fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                      const ASTContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<BreakStatement>(syntax.sourceRange());
    if (!stmtCtx.flags.has(StatementFlags::InLoop | StatementFlags::InRandSeq)) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER BreakStatement::evalImpl(EvalContext&) const {
    return ER::Break;
}

Statement& ContinueStatement::fromSyntax(Compilation& compilation,
                                         const JumpStatementSyntax& syntax,
                                         const ASTContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<ContinueStatement>(syntax.sourceRange());
    if (!stmtCtx.flags.has(StatementFlags::InLoop)) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER ContinueStatement::evalImpl(EvalContext&) const {
    return ER::Continue;
}

class UnrollVisitor : public ASTVisitor<UnrollVisitor, true, false> {
public:
    bool anyErrors = false;
    bool setupMode = true;

    explicit UnrollVisitor(const ASTContext& astCtx) :
        evalCtx(astCtx), astCtx(astCtx), comp(astCtx.getCompilation()) {
        evalCtx.pushEmptyFrame();
    }

    static void run(const ASTContext& astCtx, const ForLoopStatement& loop) {
        UnrollVisitor visitor(astCtx);
        visitor.visit(loop);

        if (std::ranges::any_of(visitor.driverMap,
                                [](auto& item) { return !item.second.empty(); })) {
            visitor.runForReal(loop);
        }
    }

    void handle(const ForLoopStatement& loop) {
        if (loop.loopVars.empty() || !loop.stopExpr || loop.steps.empty() || anyErrors) {
            loop.body.visit(*this);
            return;
        }

        // Attempt to unroll the loop. If we are unable to collect constant values
        // for all loop variables across all iterations, we won't unroll at all.
        auto handleFail = [&] {
            for (auto var : loop.loopVars)
                evalCtx.deleteLocal(var);
            loop.body.visit(*this);
        };

        SmallVector<ConstantValue*> localPtrs;
        for (auto var : loop.loopVars) {
            auto init = var->getInitializer();
            if (!init) {
                handleFail();
                return;
            }

            auto cv = init->eval(evalCtx);
            if (!cv) {
                handleFail();
                return;
            }

            localPtrs.push_back(evalCtx.createLocal(var, std::move(cv)));
        }

        // In setup mode we just do a single pass with our loop vars
        // defined to build the initial map of assignments.
        if (setupMode) {
            loop.body.visit(*this);
            return;
        }

        SmallVector<ConstantValue, 16> values;
        while (true) {
            auto cv = step() ? loop.stopExpr->eval(evalCtx) : ConstantValue();
            if (!cv) {
                handleFail();
                return;
            }

            if (!cv.isTrue())
                break;

            for (auto local : localPtrs)
                values.emplace_back(*local);

            for (auto step : loop.steps) {
                if (!step->eval(evalCtx)) {
                    handleFail();
                    return;
                }
            }
        }

        // We have all the loop iteration values. Go back through
        // and visit the loop body for each iteration.
        for (size_t i = 0; i < values.size();) {
            for (auto local : localPtrs)
                *local = std::move(values[i++]);

            loop.body.visit(*this);
            if (anyErrors)
                return;
        }
    }

    void handle(const ConditionalStatement& stmt) {
        // Evaluate the condition; if not constant visit both sides,
        // otherwise visit only the side that matches the condition.
        auto fallback = [&] {
            stmt.ifTrue.visit(*this);
            if (stmt.ifFalse)
                stmt.ifFalse->visit(*this);
        };

        if (setupMode) {
            fallback();
            return;
        }

        for (auto& cond : stmt.conditions) {
            if (cond.pattern || !step()) {
                fallback();
                return;
            }

            auto result = cond.expr->eval(evalCtx);
            if (!result) {
                fallback();
                return;
            }

            if (!result.isTrue()) {
                if (stmt.ifFalse)
                    stmt.ifFalse->visit(*this);
                return;
            }
        }

        stmt.ifTrue.visit(*this);
    }

    void handle(const ExpressionStatement& stmt) {
        step();
        if (stmt.expr.kind != ExpressionKind::Assignment)
            return;

        auto& assign = stmt.expr.as<AssignmentExpression>();
        auto& driverState = driverMap[&assign];

        if (setupMode) {
            SmallVector<std::pair<const ValueSymbol*, const Expression*>> prefixes;
            assign.left().getLongestStaticPrefixes(prefixes, evalCtx);

            for (auto [symbol, expr] : prefixes)
                driverState.emplace_back(*expr, *symbol);
        }
        else {
            for (auto& state : driverState) {
                auto bounds = ValueDriver::getBounds(*state.longestStaticPrefix, evalCtx,
                                                     *state.rootType);
                if (bounds) {
                    state.intervals.unionWith(*bounds, {}, comp.getUnrollIntervalMapAllocator());
                }
            }
        }
    }

private:
    bool step() {
        if (anyErrors || !evalCtx.step(SourceLocation::NoLocation)) {
            anyErrors = true;
            return false;
        }
        return true;
    }

    void runForReal(const ForLoopStatement& loop) {
        // Revisit the loop with setupMode turned off.
        anyErrors = false;
        setupMode = false;
        evalCtx.reset();
        evalCtx.pushEmptyFrame();
        visit(loop);

        if (anyErrors) {
            // We can't correctly apply our collected intervals if there are errors,
            // so just visit each assignment expression like normal to make sure
            // errors get issued.
            for (auto& [expr, stateVec] : driverMap) {
                auto flags = expr->isNonBlocking() ? AssignFlags::NonBlocking : AssignFlags::None;
                expr->left().requireLValue(astCtx, {}, flags);
            }
        }
        else {
            // Find our finished driver interval maps and apply them.
            auto& containingSym = astCtx.getContainingSymbol();
            for (auto& [expr, stateVec] : driverMap) {
                for (auto& state : stateVec) {
                    auto driver = comp.emplace<ValueDriver>(DriverKind::Procedural,
                                                            *state.longestStaticPrefix,
                                                            containingSym, AssignFlags::None);

                    for (auto it = state.intervals.begin(); it != state.intervals.end(); ++it)
                        state.symbol->addDriver(it.bounds(), *driver);

                    state.intervals.clear(comp.getUnrollIntervalMapAllocator());
                }
            }
        }
    }

    EvalContext evalCtx;
    const ASTContext& astCtx;
    Compilation& comp;

    struct PerAssignDriverState {
        not_null<const Expression*> longestStaticPrefix;
        not_null<const ValueSymbol*> symbol;
        not_null<const Type*> rootType;
        UnrollIntervalMap intervals;

        PerAssignDriverState(const Expression& expr, const ValueSymbol& symbol) :
            longestStaticPrefix(&expr), symbol(&symbol), rootType(&symbol.getType()) {}
    };
    flat_node_map<const AssignmentExpression*, SmallVector<PerAssignDriverState>> driverMap;
};

Statement& ForLoopStatement::fromSyntax(Compilation& compilation,
                                        const ForLoopStatementSyntax& syntax,
                                        const ASTContext& context, StatementContext& stmtCtx) {
    SmallVector<const Expression*> initializers;
    SmallVector<const VariableSymbol*> loopVars;
    bool anyBad = false;

    const bool hasVarDecls = !syntax.initializers.empty() &&
                             syntax.initializers[0]->kind == SyntaxKind::ForVariableDeclaration;
    if (hasVarDecls) {
        // The block should have already been created for us containing the
        // variable declarations.
        for (auto& var : context.scope->membersOfType<VariableSymbol>())
            loopVars.push_back(&var);
    }
    else {
        for (auto initializer : syntax.initializers) {
            auto& init = Expression::bind(initializer->as<ExpressionSyntax>(), context,
                                          ASTFlags::AssignmentAllowed);
            initializers.push_back(&init);
            anyBad |= init.bad();
        }
    }

    const Expression* stopExpr = nullptr;
    if (syntax.stopExpr)
        stopExpr = &Expression::bind(*syntax.stopExpr, context);

    SmallVector<const Expression*> steps;
    for (auto step : syntax.steps) {
        auto& expr = Expression::bind(*step, context, ASTFlags::AssignmentAllowed);
        steps.push_back(&expr);
        anyBad |= expr.bad();

        bool stepOk;
        switch (expr.kind) {
            case ExpressionKind::Invalid:
            case ExpressionKind::Assignment:
            case ExpressionKind::Call:
                stepOk = true;
                break;
            case ExpressionKind::UnaryOp: {
                auto op = expr.as<UnaryExpression>().op;
                stepOk = op == UnaryOperator::Preincrement || op == UnaryOperator::Postincrement ||
                         op == UnaryOperator::Predecrement || op == UnaryOperator::Postdecrement;
                break;
            }
            default:
                stepOk = false;
                break;
        }

        if (!stepOk) {
            anyBad = true;
            context.addDiag(diag::InvalidForStepExpression, expr.sourceRange);
        }
    }

    if (anyBad || (stopExpr && stopExpr->bad()))
        return badStmt(compilation, nullptr);

    // For purposes of checking for multiple drivers to variables, we want to
    // "unroll" this for loop if possible to allow finer grained checking of
    // longest static prefixes involving the loop variables(s).
    const bool wasFirst = !stmtCtx.flags.has(StatementFlags::InForLoop);
    auto guard = stmtCtx.enterLoop(true);
    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);

    auto result = compilation.emplace<ForLoopStatement>(initializers.copy(compilation), stopExpr,
                                                        steps.copy(compilation), bodyStmt,
                                                        syntax.sourceRange());
    result->loopVars = loopVars.copy(compilation);

    if (bodyStmt.bad())
        return badStmt(compilation, result);

    // If this is the top-level unrollable for loop, attempt the unrolling now.
    // If not top-level, just pop up the stack and let the parent loop handle us.
    if (wasFirst && !compilation.hasFlag(CompilationFlags::StrictDriverChecking) &&
        !context.scope->isUninstantiated()) {
        UnrollVisitor::run(context, *result);
    }

    return *result;
}

ER ForLoopStatement::evalImpl(EvalContext& context) const {
    for (auto init : initializers) {
        if (!init->eval(context))
            return ER::Fail;
    }

    while (true) {
        if (stopExpr) {
            auto result = stopExpr->eval(context);
            if (result.bad())
                return ER::Fail;

            if (!result.isTrue())
                break;
        }

        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }

        for (auto step : steps) {
            if (!step->eval(context))
                return ER::Fail;
        }
    }

    return ER::Success;
}

void ForLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("initializers");
    for (auto ini : initializers) {
        serializer.serialize(*ini);
    }
    serializer.endArray();

    if (stopExpr)
        serializer.write("stopExpr", *stopExpr);

    serializer.startArray("steps");
    for (auto step : steps) {
        serializer.serialize(*step);
    }
    serializer.endArray();

    serializer.write("body", body);
}

Statement& RepeatLoopStatement::fromSyntax(Compilation& compilation,
                                           const LoopStatementSyntax& syntax,
                                           const ASTContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();
    auto& countExpr = Expression::bind(*syntax.expr, context);

    bool bad = countExpr.bad();
    if (!bad && !countExpr.type->isNumeric()) {
        context.addDiag(diag::RepeatNotNumeric, countExpr.sourceRange);
        bad = true;
    }

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<RepeatLoopStatement>(countExpr, bodyStmt,
                                                           syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER RepeatLoopStatement::evalImpl(EvalContext& context) const {
    auto cv = count.eval(context);
    if (cv.bad())
        return ER::Fail;

    std::optional<int64_t> oc = cv.integer().as<int64_t>();
    if (!oc || oc < 0) {
        if (cv.integer().hasUnknown())
            oc = 0;
        else {
            auto& diag = context.addDiag(diag::ValueOutOfRange, count.sourceRange);
            diag << cv << 0 << INT64_MAX;
            return ER::Fail;
        }
    }

    int64_t c = *oc;
    for (int64_t i = 0; i < c; i++) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void RepeatLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count);
    serializer.write("body", body);
}

const Expression* ForeachLoopStatement::buildLoopDims(const ForeachLoopListSyntax& loopList,
                                                      ASTContext& context,
                                                      SmallVectorBase<LoopDim>& dims) {
    // Find the array over which we are looping. Make sure it's actually iterable:
    // - Must be a referenceable variable, class property, etc.
    // - Type can be:
    //    - Any kind of array
    //    - Any multi-dimensional integral type
    //    - A string
    auto& comp = context.getCompilation();
    auto& arrayRef = Expression::bind(*loopList.arrayName, context);
    if (arrayRef.bad()) {
        // Create placeholder iterator symbols to prevent downstream errors.
        for (auto loopVar : loopList.loopVariables) {
            if (loopVar->kind == SyntaxKind::IdentifierName) {
                auto idName = loopVar->as<IdentifierNameSyntax>().identifier;
                auto it = comp.emplace<IteratorSymbol>(idName.valueText(), idName.location(),
                                                       comp.getErrorType(), comp.getErrorType());
                it->nextTemp = std::exchange(context.firstTempVar, it);
                dims.push_back({std::nullopt, it});
            }
        }
        return nullptr;
    }

    const Type* type = arrayRef.type;
    auto arraySym = arrayRef.getSymbolReference();
    if (!arraySym || !type->isIterable()) {
        context.addDiag(diag::NotAnArray, arrayRef.sourceRange);
        return nullptr;
    }

    // Build iterator symbols for each loop variable.
    bool skippedAny = false;
    for (auto loopVar : loopList.loopVariables) {
        // If type is null, we've run out of dimensions so there were too many
        // loop variables supplied.
        if (!type || type->isScalar()) {
            context.addDiag(diag::TooManyForeachVars, loopList.loopVariables.sourceRange())
                << *arrayRef.type;
            return nullptr;
        }

        if (type->hasFixedRange())
            dims.push_back({type->getFixedRange()});
        else
            dims.emplace_back();

        const Type& currType = *type;
        type = type->getArrayElementType();

        // Empty iterator names indicate that we skip this dimension.
        if (loopVar->kind == SyntaxKind::EmptyIdentifierName) {
            skippedAny = true;
            continue;
        }

        auto& idName = loopVar->as<IdentifierNameSyntax>();
        std::string_view name = idName.identifier.valueText();

        // If we previously had skipped dimensions this one can't be dynamically
        // sized (there would be no way to reach it during iteration).
        if (!dims.back().range && skippedAny) {
            context.addDiag(diag::ForeachDynamicDimAfterSkipped, idName.sourceRange()) << name;
            return nullptr;
        }

        if (name == arraySym->name) {
            context.addDiag(diag::LoopVarShadowsArray, loopVar->sourceRange()) << name;
            return nullptr;
        }

        // The type of the iterator is typically an int, unless this dimension
        // is an associative array in which case it's the index type.
        const Type* indexType;
        if (currType.isAssociativeArray()) {
            indexType = currType.getAssociativeIndexType();
            if (!indexType) {
                context.addDiag(diag::ForeachWildcardIndex, loopVar->sourceRange())
                    << loopList.arrayName->sourceRange();
                indexType = &comp.getErrorType();
            }
        }
        else {
            indexType = &comp.getIntType();
        }

        // Build the iterator variable and hook it up to our new context's
        // linked list of iterators.
        auto it = comp.emplace<IteratorSymbol>(name, idName.identifier.location(), currType,
                                               *indexType);
        it->nextTemp = std::exchange(context.firstTempVar, it);
        dims.back().loopVar = it;
    }

    return &arrayRef;
}

Statement& ForeachLoopStatement::fromSyntax(Compilation& compilation,
                                            const ForeachLoopStatementSyntax& syntax,
                                            const ASTContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    auto& arrayRef = Expression::bind(*syntax.loopList->arrayName, context);
    SLANG_ASSERT(!arrayRef.bad());

    // Loop variables were already built in the containing block when it was elaborated,
    // so we just have to find them and associate them with the correct dim ranges here.
    SmallVector<LoopDim, 4> dims;
    const Type* type = arrayRef.type;
    auto range = context.scope->membersOfType<IteratorSymbol>();
    auto itIt = range.begin();

    for (auto loopVar : syntax.loopList->loopVariables) {
        if (type->hasFixedRange())
            dims.push_back({type->getFixedRange()});
        else
            dims.emplace_back();

        type = type->getArrayElementType();

        if (loopVar->kind == SyntaxKind::EmptyIdentifierName)
            continue;

        SLANG_ASSERT(itIt != range.end());
        SLANG_ASSERT(itIt->name == loopVar->as<IdentifierNameSyntax>().identifier.valueText());

        IteratorSymbol* it = const_cast<IteratorSymbol*>(&*itIt);
        dims.back().loopVar = it;
        itIt++;
    }

    SLANG_ASSERT(itIt == range.end());

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<ForeachLoopStatement>(arrayRef, dims.copy(compilation),
                                                            bodyStmt, syntax.sourceRange());
    if (bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER ForeachLoopStatement::evalImpl(EvalContext& context) const {
    // If there are no loop dimensions, this does nothing.
    if (loopDims.empty())
        return ER::Success;

    ConstantValue cv = arrayRef.eval(context);
    if (!cv)
        return ER::Fail;

    ER result = evalRecursive(context, cv, loopDims);
    if (result == ER::Break || result == ER::Continue)
        return ER::Success;

    return result;
}

ER ForeachLoopStatement::evalRecursive(EvalContext& context, const ConstantValue& cv,
                                       std::span<const LoopDim> currDims) const {
    // If there is no loop var just skip this index.
    auto& dim = currDims[0];
    if (!dim.loopVar) {
        // Shouldn't ever be at the end here.
        return evalRecursive(context, nullptr, currDims.subspan(1));
    }

    auto local = context.createLocal(dim.loopVar);

    // If this is an associative array, looping happens over the keys.
    if (cv.isMap()) {
        auto& map = *cv.map();
        for (auto& [key, val] : map) {
            *local = key;

            ER result;
            if (currDims.size() > 1)
                result = evalRecursive(context, val, currDims.subspan(1));
            else
                result = body.eval(context);

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else if (cv.isQueue()) {
        auto& q = *cv.queue();
        for (size_t i = 0; i < q.size(); i++) {
            *local = SVInt(32, i, true);

            ER result;
            if (currDims.size() > 1)
                result = evalRecursive(context, q[i], currDims.subspan(1));
            else
                result = body.eval(context);

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else if (cv.isString()) {
        SLANG_ASSERT(currDims.size() == 1);

        auto& str = cv.str();
        for (size_t i = 0; i < str.size(); i++) {
            *local = SVInt(32, i, true);

            ER result = body.eval(context);
            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else {
        std::span<const ConstantValue> elements;
        if (cv.isUnpacked())
            elements = cv.elements();

        ConstantRange range;
        bool isLittleEndian;
        if (dim.range) {
            range = *dim.range;
            isLittleEndian = range.isLittleEndian();
        }
        else {
            range = {0, int32_t(elements.size()) - 1};
            isLittleEndian = false;
        }

        for (int32_t i = range.left; isLittleEndian ? i >= range.right : i <= range.right;
             isLittleEndian ? i-- : i++) {

            *local = SVInt(32, uint64_t(i), true);

            ER result;
            if (currDims.size() > 1) {
                size_t index = size_t(i);
                if (dim.range)
                    index = (size_t)range.reverse().translateIndex(i);

                result = evalRecursive(context, elements.empty() ? nullptr : elements[index],
                                       currDims.subspan(1));
            }
            else {
                result = body.eval(context);
            }

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void ForeachLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("arrayRef", arrayRef);

    serializer.startArray("loopDims");
    for (auto& r : loopDims) {
        serializer.startObject();
        serializer.write("range", r.range ? r.range->toString() : "[]");
        if (r.loopVar)
            serializer.write("var", *r.loopVar);
        serializer.endObject();
    }
    serializer.endArray();

    serializer.write("body", body);
}

Statement& WhileLoopStatement::fromSyntax(Compilation& compilation,
                                          const LoopStatementSyntax& syntax,
                                          const ASTContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    bool bad = false;
    auto& condExpr = Expression::bind(*syntax.expr, context);
    if (!context.requireBooleanConvertible(condExpr))
        bad = true;

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<WhileLoopStatement>(condExpr, bodyStmt, syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER WhileLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        auto cv = cond.eval(context);
        if (cv.bad())
            return ER::Fail;

        if (!cv.isTrue())
            break;

        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void WhileLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("body", body);
}

Statement& DoWhileLoopStatement::fromSyntax(Compilation& compilation,
                                            const DoWhileStatementSyntax& syntax,
                                            const ASTContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    bool bad = false;
    auto& condExpr = Expression::bind(*syntax.expr, context);
    if (!context.requireBooleanConvertible(condExpr))
        bad = true;

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<DoWhileLoopStatement>(condExpr, bodyStmt,
                                                            syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER DoWhileLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }

        auto cv = cond.eval(context);
        if (cv.bad())
            return ER::Fail;

        if (!cv.isTrue())
            break;
    }

    return ER::Success;
}

void DoWhileLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("body", body);
}

Statement& ForeverLoopStatement::fromSyntax(Compilation& compilation,
                                            const ForeverStatementSyntax& syntax,
                                            const ASTContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<ForeverLoopStatement>(bodyStmt, syntax.sourceRange());
    if (bodyStmt.bad())
        return badStmt(compilation, result);

    return *result;
}

ER ForeverLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void ForeverLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("body", body);
}

} // namespace slang::ast
