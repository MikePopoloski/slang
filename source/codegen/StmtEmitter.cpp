//------------------------------------------------------------------------------
// StmtEmitter.cpp
// Emission of SystemVerilog statements to LLVM IR.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "CodegenImpl.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>

#include "slang/ast/ASTVisitor.h"

namespace slang::codegen {

namespace {

struct StmtEmitter {
    FunctionEmitter& fe;
    IRBuilder& builder;

    explicit StmtEmitter(FunctionEmitter& fe) : fe(fe), builder(fe.builder) {}

    void nextStmt(const Statement& s);

    void visit(const InvalidStatement& s);
    void visit(const EmptyStatement& s);
    void visit(const StatementList& s);
    void visit(const BlockStatement& s);
    void visit(const ExpressionStatement& s);
    void visit(const VariableDeclStatement& s);
    void visit(const ReturnStatement& s);
    void visit(const BreakStatement& s);
    void visit(const ContinueStatement& s);
    void visit(const ConditionalStatement& s);
    void visit(const CaseStatement& s);
    void visit(const ForLoopStatement& s);
    void visit(const WhileLoopStatement& s);
    void visit(const DoWhileLoopStatement& s);
    void visit(const RepeatLoopStatement& s);
    void visit(const ForeverLoopStatement& s);
    void visit(const ForeachLoopStatement& s);
    void visit(const DisableStatement& s);
    void visit(const PatternCaseStatement& s);
    void visit(const TimedStatement& s);
    void visit(const ImmediateAssertionStatement& s);
    void visit(const ConcurrentAssertionStatement& s);
    void visit(const DisableForkStatement& s);
    void visit(const WaitStatement& s);
    void visit(const WaitForkStatement& s);
    void visit(const WaitOrderStatement& s);
    void visit(const EventTriggerStatement& s);
    void visit(const ProceduralAssignStatement& s);
    void visit(const ProceduralDeassignStatement& s);
    void visit(const RandCaseStatement& s);
    void visit(const RandSequenceStatement& s);
    void visit(const ProceduralCheckerStatement& s);

    void emitInitializer(const VariableSymbol& var, llvm::Value* addr);
};

void StmtEmitter::nextStmt(const Statement& s) {
    // If we're in unreachable code just ignore the statement.
    auto bb = builder.GetInsertBlock();
    if (!bb || bb->getTerminator())
        return;

    // Otherwise visit the statement.
    s.visit(*this);
}

void StmtEmitter::visit(const InvalidStatement&) {
    // Ignore these.
}

void StmtEmitter::visit(const EmptyStatement&) {
    // Nothing to do.
}

void StmtEmitter::visit(const StatementList& s) {
    for (auto stmt : s.list)
        nextStmt(*stmt);
}

void StmtEmitter::visit(const BlockStatement& s) {
    if (s.blockKind != StatementBlockKind::Sequential)
        SLANG_UNIMPLEMENTED;

    nextStmt(s.body);
}

void StmtEmitter::visit(const ExpressionStatement& s) {
    // Emit the expression, drop the result.
    fe.emitExpr(s.expr);
}

void StmtEmitter::visit(const VariableDeclStatement& s) {
    auto& var = s.symbol;
    if (var.lifetime == VariableLifetime::Static)
        SLANG_UNIMPLEMENTED;

    auto alloca = fe.createLocal(var);
    emitInitializer(var, alloca);
}

void StmtEmitter::visit(const ReturnStatement& s) {
    SLANG_ASSERT(bool(s.expr) == bool(fe.returnVal));
    if (s.expr)
        builder.CreateStore(fe.emitExpr(*s.expr), fe.returnVal);
    fe.emitBranch(fe.returnBlock);
}

void StmtEmitter::visit(const BreakStatement&) {
    SLANG_ASSERT(fe.breakTarget);
    builder.CreateBr(fe.breakTarget);
    builder.ClearInsertionPoint();
}

void StmtEmitter::visit(const ContinueStatement&) {
    SLANG_ASSERT(fe.continueTarget);
    builder.CreateBr(fe.continueTarget);
    builder.ClearInsertionPoint();
}

void StmtEmitter::visit(const ConditionalStatement& s) {
    if (s.conditions.size() > 1 || s.conditions[0].pattern)
        SLANG_UNIMPLEMENTED;
    if (s.check != UniquePriorityCheck::None)
        SLANG_UNIMPLEMENTED;

    // If we have a known constant condition avoid emitting the unneeded branch.
    auto cv = fe.tryEval(*s.conditions[0].expr);
    if (cv.isInteger() && !cv.integer().hasUnknown()) {
        auto executed = &s.ifTrue;
        if (!cv.isTrue())
            executed = s.ifFalse;

        if (executed)
            nextStmt(*executed);
        return;
    }

    auto thenBB = fe.createBasicBlock("if.then");
    auto mergeBB = fe.createBasicBlock("if.end");
    auto elseBB = s.ifFalse ? fe.createBasicBlock("if.else") : mergeBB;

    // TODO: handle ambiguous unknown case
    auto condVal = fe.emitCond(*s.conditions[0].expr);
    builder.CreateCondBr(condVal, thenBB, elseBB);

    fe.emitBlock(thenBB);
    fe.emitStmt(s.ifTrue);
    fe.emitBranch(mergeBB);

    if (s.ifFalse) {
        fe.emitBlock(elseBB);
        fe.emitStmt(*s.ifFalse);
        fe.emitBranch(mergeBB);
    }

    fe.emitBlock(mergeBB);
}

void StmtEmitter::visit(const CaseStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ForLoopStatement& s) {
    // Emit initializers up front.
    for (auto init : s.initializers)
        fe.emitExpr(*init);

    // Start the loop with a block that tests the condition. If there's
    // an increment, the continue scope will be overwritten later.
    auto condBB = fe.createBasicBlock("for.cond");
    fe.emitBlock(condBB);

    // If the for loop doesn't have an increment we can just use the condition as
    // the continue block. Otherwise, we can form the continue block now.
    llvm::BasicBlock* stepBB;
    if (s.steps.empty())
        stepBB = condBB;
    else
        stepBB = fe.createBasicBlock("for.step");

    auto exitBB = fe.createBasicBlock("for.exit");
    auto savedBreak = std::exchange(fe.breakTarget, exitBB);
    auto savedContinue = std::exchange(fe.continueTarget, stepBB);

    if (s.stopExpr) {
        // As long as the condition is true, iterate the loop.
        auto bodyBB = fe.createBasicBlock("for.body");
        builder.CreateCondBr(fe.emitCond(*s.stopExpr), bodyBB, exitBB);
        fe.emitBlock(bodyBB);
    }
    else {
        // If no stop expression, don't even create a new block for the body,
        // just fall into it.
    }

    nextStmt(s.body);

    // If there are steps, emit them next.
    if (!s.steps.empty()) {
        fe.emitBlock(stepBB);
        for (auto step : s.steps)
            fe.emitExpr(*step);
    }

    fe.breakTarget = savedBreak;
    fe.continueTarget = savedContinue;
    fe.emitBranch(condBB);
    fe.emitBlock(exitBB, /* isFinished */ true);
}

void StmtEmitter::visit(const WhileLoopStatement& s) {
    // Emit the header for the loop, which will also become
    // the continue target.
    auto condBB = fe.createBasicBlock("while.cond");
    fe.emitBlock(condBB);

    // Create an exit block for when the condition fails, which will
    // also become the break target.
    auto exitBB = fe.createBasicBlock("while.exit");
    auto savedBreak = std::exchange(fe.breakTarget, exitBB);
    auto savedContinue = std::exchange(fe.continueTarget, condBB);

    auto bodyBB = fe.createBasicBlock("while.body");
    builder.CreateCondBr(fe.emitCond(s.cond), bodyBB, exitBB);

    fe.emitBlock(bodyBB);
    nextStmt(s.body);

    fe.breakTarget = savedBreak;
    fe.continueTarget = savedContinue;
    fe.emitBranch(condBB);
    fe.emitBlock(exitBB, /* isFinished */ true);
}

void StmtEmitter::visit(const DoWhileLoopStatement& s) {
    auto exitBB = fe.createBasicBlock("do.exit");
    auto condBB = fe.createBasicBlock("do.cond");
    auto savedBreak = std::exchange(fe.breakTarget, exitBB);
    auto savedContinue = std::exchange(fe.continueTarget, condBB);

    // Go straight into the body.
    auto bodyBB = fe.createBasicBlock("do.body");
    fe.emitBlock(bodyBB);
    nextStmt(s.body);

    fe.emitBlock(condBB);

    fe.breakTarget = savedBreak;
    fe.continueTarget = savedContinue;
    builder.CreateCondBr(fe.emitCond(s.cond), bodyBB, exitBB);

    fe.emitBlock(exitBB, /* isFinished */ true);
}

void StmtEmitter::visit(const RepeatLoopStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ForeverLoopStatement& s) {
    auto exitBB = fe.createBasicBlock("forever.exit");
    auto bodyBB = fe.createBasicBlock("forever.body");
    auto savedBreak = std::exchange(fe.breakTarget, exitBB);
    auto savedContinue = std::exchange(fe.continueTarget, bodyBB);

    // Go straight into the body.
    fe.emitBlock(bodyBB);
    nextStmt(s.body);

    // Unconditionally jump back to the loop start.
    fe.emitBranch(bodyBB);

    fe.breakTarget = savedBreak;
    fe.continueTarget = savedContinue;
    fe.emitBlock(exitBB, /* isFinished */ true);
}

void StmtEmitter::visit(const ForeachLoopStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const DisableStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const PatternCaseStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const TimedStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ImmediateAssertionStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ConcurrentAssertionStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const DisableForkStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const WaitStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const WaitForkStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const WaitOrderStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const EventTriggerStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ProceduralAssignStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ProceduralDeassignStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const RandCaseStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const RandSequenceStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::visit(const ProceduralCheckerStatement&) {
    SLANG_UNIMPLEMENTED;
}

void StmtEmitter::emitInitializer(const VariableSymbol& var, llvm::Value* addr) {
    SLANG_ASSERT(var.lifetime == VariableLifetime::Automatic);

    if (auto init = var.getInitializer()) {
        auto val = fe.emitExpr(*init);
        builder.CreateStore(val, addr);
    }
    else {
        // TODO: set default value
        SLANG_UNIMPLEMENTED;
    }
}

} // anonymous namespace

void FunctionEmitter::emitStmt(const Statement& stmt) {
    StmtEmitter emitter{*this};
    emitter.nextStmt(stmt);
}

} // namespace slang::codegen
