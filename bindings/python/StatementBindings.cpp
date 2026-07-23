//------------------------------------------------------------------------------
// StatementBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/syntax/AllSyntax.h"

void registerStatements(nb::module_& m) {
    EXPOSE_ENUM(m, StatementKind);
    EXPOSE_ENUM(m, CaseStatementCondition);
    EXPOSE_ENUM(m, UniquePriorityCheck);

    nb::class_<Statement> stmt(m, "Statement");
    stmt.def_ro("kind", &Statement::kind)
        .def_ro("syntax", &Statement::syntax)
        .def_ro("sourceRange", &Statement::sourceRange)
        .def_prop_ro("bad", &Statement::bad)
        .def("eval", &Statement::eval, "context"_a)
        .def("visit", &pyASTVisit<Statement>, "f"_a = nb::none(), "lookup_table"_a = nb::none(),
             PyASTVisitor::doc)
        .def("__repr__", [](const Statement& self) {
            return fmt::format("Statement(StatementKind.{})", toString(self.kind));
        });

    nb::enum_<Statement::EvalResult>(m, "EvalResult")
        .value("Fail", Statement::EvalResult::Fail)
        .value("Success", Statement::EvalResult::Success)
        .value("Return", Statement::EvalResult::Return)
        .value("Break", Statement::EvalResult::Break)
        .value("Continue", Statement::EvalResult::Continue)
        .value("Disable", Statement::EvalResult::Disable);

    nb::class_<InvalidStatement, Statement>(m, "InvalidStatement");
    nb::class_<EmptyStatement, Statement>(m, "EmptyStatement");
    nb::class_<BreakStatement, Statement>(m, "BreakStatement");
    nb::class_<ContinueStatement, Statement>(m, "ContinueStatement");
    nb::class_<DisableForkStatement, Statement>(m, "DisableForkStatement");
    nb::class_<WaitForkStatement, Statement>(m, "WaitForkStatement");

    nb::class_<StatementList, Statement>(m, "StatementList").def_ro("list", &StatementList::list);

    nb::class_<BlockStatement, Statement>(m, "BlockStatement")
        .def_ro("blockSymbol", &BlockStatement::blockSymbol)
        .def_ro("blockKind", &BlockStatement::blockKind)
        .def_prop_ro("body", [](const BlockStatement& self) { return &self.body; });

    nb::class_<ReturnStatement, Statement>(m, "ReturnStatement")
        .def_ro("expr", &ReturnStatement::expr);

    nb::class_<DisableStatement, Statement>(m, "DisableStatement")
        .def_prop_ro("target", [](const DisableStatement& self) { return &self.target; });

    nb::class_<VariableDeclStatement, Statement>(m, "VariableDeclStatement")
        .def_prop_ro("symbol", [](const VariableDeclStatement& self) { return &self.symbol; });

    nb::class_<ConditionalStatement, Statement> condStmt(m, "ConditionalStatement");
    condStmt.def_ro("conditions", &ConditionalStatement::conditions)
        .def_ro("check", &ConditionalStatement::check)
        .def_ro("ifFalse", &ConditionalStatement::ifFalse)
        .def_prop_ro("ifTrue", [](const ConditionalStatement& self) { return &self.ifTrue; });

    nb::class_<ConditionalStatement::Condition>(condStmt, "Condition")
        .def_ro("expr", &ConditionalStatement::Condition::expr)
        .def_ro("pattern", &ConditionalStatement::Condition::pattern);

    nb::class_<CaseStatement, Statement> caseStmt(m, "CaseStatement");
    caseStmt.def_ro("items", &CaseStatement::items)
        .def_ro("defaultCase", &CaseStatement::defaultCase)
        .def_ro("condition", &CaseStatement::condition)
        .def_ro("check", &CaseStatement::check)
        .def_prop_ro("expr", [](const CaseStatement& self) { return &self.expr; });

    nb::class_<CaseStatement::ItemGroup>(caseStmt, "ItemGroup")
        .def_ro("expressions", &CaseStatement::ItemGroup::expressions)
        .def_ro("stmt", &CaseStatement::ItemGroup::stmt);

    nb::class_<PatternCaseStatement, Statement> patternCaseStmt(m, "PatternCaseStatement");
    patternCaseStmt.def_ro("items", &PatternCaseStatement::items)
        .def_ro("defaultCase", &PatternCaseStatement::defaultCase)
        .def_ro("condition", &PatternCaseStatement::condition)
        .def_ro("check", &PatternCaseStatement::check)
        .def_prop_ro("expr", [](const PatternCaseStatement& self) { return &self.expr; });

    nb::class_<PatternCaseStatement::ItemGroup>(patternCaseStmt, "ItemGroup")
        .def_ro("pattern", &PatternCaseStatement::ItemGroup::pattern)
        .def_ro("filter", &PatternCaseStatement::ItemGroup::filter)
        .def_ro("stmt", &PatternCaseStatement::ItemGroup::stmt);

    nb::class_<ForLoopStatement, Statement>(m, "ForLoopStatement")
        .def_ro("initializers", &ForLoopStatement::initializers)
        .def_ro("loopVars", &ForLoopStatement::loopVars)
        .def_ro("stopExpr", &ForLoopStatement::stopExpr)
        .def_ro("steps", &ForLoopStatement::steps)
        .def_prop_ro("body", [](const ForLoopStatement& self) { return &self.body; });

    nb::class_<ForeachLoopStatement, Statement> foreachStmt(m, "ForeachLoopStatement");
    foreachStmt.def_ro("loopDims", &ForeachLoopStatement::loopDims)
        .def_prop_ro("arrayRef", [](const ForeachLoopStatement& self) { return &self.arrayRef; })
        .def_prop_ro("body", [](const ForeachLoopStatement& self) { return &self.body; });

    nb::class_<ForeachLoopStatement::LoopDim>(foreachStmt, "LoopDim")
        .def_ro("range", &ForeachLoopStatement::LoopDim::range)
        .def_ro("loopVar", &ForeachLoopStatement::LoopDim::loopVar);

    nb::class_<RepeatLoopStatement, Statement>(m, "RepeatLoopStatement")
        .def_prop_ro("count", [](const RepeatLoopStatement& self) { return &self.count; })
        .def_prop_ro("body", [](const RepeatLoopStatement& self) { return &self.body; });

    nb::class_<WhileLoopStatement, Statement>(m, "WhileLoopStatement")
        .def_prop_ro("cond", [](const WhileLoopStatement& self) { return &self.cond; })
        .def_prop_ro("body", [](const WhileLoopStatement& self) { return &self.body; });

    nb::class_<DoWhileLoopStatement, Statement>(m, "DoWhileLoopStatement")
        .def_prop_ro("cond", [](const DoWhileLoopStatement& self) { return &self.cond; })
        .def_prop_ro("body", [](const DoWhileLoopStatement& self) { return &self.body; });

    nb::class_<ForeverLoopStatement, Statement>(m, "ForeverLoopStatement")
        .def_prop_ro("body", [](const ForeverLoopStatement& self) { return &self.body; });

    nb::class_<ExpressionStatement, Statement>(m, "ExpressionStatement")
        .def_prop_ro("expr", [](const ExpressionStatement& self) { return &self.expr; });

    nb::class_<TimedStatement, Statement>(m, "TimedStatement")
        .def_prop_ro("timing", [](const TimedStatement& self) { return &self.timing; })
        .def_prop_ro("stmt", [](const TimedStatement& self) { return &self.stmt; });

    nb::class_<ImmediateAssertionStatement, Statement>(m, "ImmediateAssertionStatement")
        .def_prop_ro("cond", [](const ImmediateAssertionStatement& self) { return &self.cond; })
        .def_ro("ifTrue", &ImmediateAssertionStatement::ifTrue)
        .def_ro("ifFalse", &ImmediateAssertionStatement::ifFalse)
        .def_ro("assertionKind", &ImmediateAssertionStatement::assertionKind)
        .def_ro("isDeferred", &ImmediateAssertionStatement::isDeferred)
        .def_ro("isFinal", &ImmediateAssertionStatement::isFinal);

    nb::class_<ConcurrentAssertionStatement, Statement>(m, "ConcurrentAssertionStatement")
        .def_prop_ro("propertySpec",
                     [](const ConcurrentAssertionStatement& self) { return &self.propertySpec; })
        .def_ro("ifTrue", &ConcurrentAssertionStatement::ifTrue)
        .def_ro("ifFalse", &ConcurrentAssertionStatement::ifFalse)
        .def_ro("assertionKind", &ConcurrentAssertionStatement::assertionKind);

    nb::class_<WaitStatement, Statement>(m, "WaitStatement")
        .def_prop_ro("cond", [](const WaitStatement& self) { return &self.cond; })
        .def_prop_ro("stmt", [](const WaitStatement& self) { return &self.stmt; });

    nb::class_<WaitOrderStatement, Statement>(m, "WaitOrderStatement")
        .def_ro("ifTrue", &WaitOrderStatement::ifTrue)
        .def_ro("ifFalse", &WaitOrderStatement::ifFalse)
        .def_ro("events", &WaitOrderStatement::events);

    nb::class_<EventTriggerStatement, Statement>(m, "EventTriggerStatement")
        .def_prop_ro("target", [](const EventTriggerStatement& self) { return &self.target; })
        .def_ro("timing", &EventTriggerStatement::timing)
        .def_ro("isNonBlocking", &EventTriggerStatement::isNonBlocking);

    nb::class_<ProceduralAssignStatement, Statement>(m, "ProceduralAssignStatement")
        .def_prop_ro("assignment",
                     [](const ProceduralAssignStatement& self) { return &self.assignment; })
        .def_ro("isForce", &ProceduralAssignStatement::isForce);

    nb::class_<ProceduralDeassignStatement, Statement>(m, "ProceduralDeassignStatement")
        .def_prop_ro("lvalue", [](const ProceduralDeassignStatement& self) { return &self.lvalue; })
        .def_ro("isRelease", &ProceduralDeassignStatement::isRelease);

    nb::class_<RandCaseStatement, Statement> randCaseStmt(m, "RandCaseStatement");
    randCaseStmt.def_ro("items", &RandCaseStatement::items);

    nb::class_<RandCaseStatement::Item>(randCaseStmt, "Item")
        .def_ro("expr", &RandCaseStatement::Item::expr)
        .def_ro("stmt", &RandCaseStatement::Item::stmt);

    nb::class_<RandSequenceStatement, Statement>(m, "RandSequenceStatement")
        .def_ro("firstProduction", &RandSequenceStatement::firstProduction);

    nb::class_<ProceduralCheckerStatement, Statement>(m, "ProceduralCheckerStatement")
        .def_ro("instances", &ProceduralCheckerStatement::instances);
}
