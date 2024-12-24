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

void registerStatements(py::module_& m) {
    EXPOSE_ENUM(m, StatementKind);
    EXPOSE_ENUM(m, CaseStatementCondition);
    EXPOSE_ENUM(m, UniquePriorityCheck);

    py::class_<Statement> stmt(m, "Statement");
    stmt.def_readonly("kind", &Statement::kind)
        .def_readonly("syntax", &Statement::syntax)
        .def_readonly("sourceRange", &Statement::sourceRange)
        .def_property_readonly("bad", &Statement::bad)
        .def("eval", &Statement::eval, "context"_a)
        .def("visit", &pyASTVisit<Statement>, "f"_a, PyASTVisitor::doc)
        .def("__repr__", [](const Statement& self) {
            return fmt::format("Statement(StatementKind.{})", toString(self.kind));
        });

    py::enum_<Statement::EvalResult>(stmt, "EvalResult")
        .value("Fail", Statement::EvalResult::Fail)
        .value("Success", Statement::EvalResult::Success)
        .value("Return", Statement::EvalResult::Return)
        .value("Break", Statement::EvalResult::Break)
        .value("Continue", Statement::EvalResult::Continue)
        .value("Disable", Statement::EvalResult::Disable);

    py::class_<InvalidStatement, Statement>(m, "InvalidStatement");
    py::class_<EmptyStatement, Statement>(m, "EmptyStatement");
    py::class_<BreakStatement, Statement>(m, "BreakStatement");
    py::class_<ContinueStatement, Statement>(m, "ContinueStatement");
    py::class_<DisableForkStatement, Statement>(m, "DisableForkStatement");
    py::class_<WaitForkStatement, Statement>(m, "WaitForkStatement");

    py::class_<StatementList, Statement>(m, "StatementList")
        .def_readonly("list", &StatementList::list);

    py::class_<BlockStatement, Statement>(m, "BlockStatement")
        .def_readonly("blockSymbol", &BlockStatement::blockSymbol)
        .def_readonly("blockKind", &BlockStatement::blockKind)
        .def_property_readonly("body", [](const BlockStatement& self) { return &self.body; });

    py::class_<ReturnStatement, Statement>(m, "ReturnStatement")
        .def_readonly("expr", &ReturnStatement::expr);

    py::class_<DisableStatement, Statement>(m, "DisableStatement")
        .def_property_readonly("target", [](const DisableStatement& self) { return &self.target; });

    py::class_<VariableDeclStatement, Statement>(m, "VariableDeclStatement")
        .def_property_readonly("symbol",
                               [](const VariableDeclStatement& self) { return &self.symbol; });

    py::class_<ConditionalStatement, Statement> condStmt(m, "ConditionalStatement");
    condStmt.def_readonly("conditions", &ConditionalStatement::conditions)
        .def_readonly("check", &ConditionalStatement::check)
        .def_readonly("ifFalse", &ConditionalStatement::ifFalse)
        .def_property_readonly("ifTrue",
                               [](const ConditionalStatement& self) { return &self.ifTrue; });

    py::class_<ConditionalStatement::Condition>(condStmt, "Condition")
        .def_readonly("expr", &ConditionalStatement::Condition::expr)
        .def_readonly("pattern", &ConditionalStatement::Condition::pattern);

    py::class_<CaseStatement, Statement> caseStmt(m, "CaseStatement");
    caseStmt.def_readonly("items", &CaseStatement::items)
        .def_readonly("defaultCase", &CaseStatement::defaultCase)
        .def_readonly("condition", &CaseStatement::condition)
        .def_readonly("check", &CaseStatement::check)
        .def_property_readonly("expr", [](const CaseStatement& self) { return &self.expr; });

    py::class_<CaseStatement::ItemGroup>(caseStmt, "ItemGroup")
        .def_readonly("expressions", &CaseStatement::ItemGroup::expressions)
        .def_readonly("stmt", &CaseStatement::ItemGroup::stmt);

    py::class_<PatternCaseStatement, Statement> patternCaseStmt(m, "PatternCaseStatement");
    patternCaseStmt.def_readonly("items", &PatternCaseStatement::items)
        .def_readonly("defaultCase", &PatternCaseStatement::defaultCase)
        .def_readonly("condition", &PatternCaseStatement::condition)
        .def_readonly("check", &PatternCaseStatement::check)
        .def_property_readonly("expr", [](const PatternCaseStatement& self) { return &self.expr; });

    py::class_<PatternCaseStatement::ItemGroup>(patternCaseStmt, "ItemGroup")
        .def_readonly("pattern", &PatternCaseStatement::ItemGroup::pattern)
        .def_readonly("filter", &PatternCaseStatement::ItemGroup::filter)
        .def_readonly("stmt", &PatternCaseStatement::ItemGroup::stmt);

    py::class_<ForLoopStatement, Statement>(m, "ForLoopStatement")
        .def_readonly("initializers", &ForLoopStatement::initializers)
        .def_readonly("loopVars", &ForLoopStatement::loopVars)
        .def_readonly("stopExpr", &ForLoopStatement::stopExpr)
        .def_readonly("steps", &ForLoopStatement::steps)
        .def_property_readonly("body", [](const ForLoopStatement& self) { return &self.body; });

    py::class_<ForeachLoopStatement, Statement> foreachStmt(m, "ForeachLoopStatement");
    foreachStmt.def_readonly("loopDims", &ForeachLoopStatement::loopDims)
        .def_property_readonly("arrayRef",
                               [](const ForeachLoopStatement& self) { return &self.arrayRef; })
        .def_property_readonly("body", [](const ForeachLoopStatement& self) { return &self.body; });

    py::class_<ForeachLoopStatement::LoopDim>(foreachStmt, "LoopDim")
        .def_readonly("range", &ForeachLoopStatement::LoopDim::range)
        .def_readonly("loopVar", &ForeachLoopStatement::LoopDim::loopVar);

    py::class_<RepeatLoopStatement, Statement>(m, "RepeatLoopStatement")
        .def_property_readonly("count", [](const RepeatLoopStatement& self) { return &self.count; })
        .def_property_readonly("body", [](const RepeatLoopStatement& self) { return &self.body; });

    py::class_<WhileLoopStatement, Statement>(m, "WhileLoopStatement")
        .def_property_readonly("cond", [](const WhileLoopStatement& self) { return &self.cond; })
        .def_property_readonly("body", [](const WhileLoopStatement& self) { return &self.body; });

    py::class_<DoWhileLoopStatement, Statement>(m, "DoWhileLoopStatement")
        .def_property_readonly("cond", [](const DoWhileLoopStatement& self) { return &self.cond; })
        .def_property_readonly("body", [](const DoWhileLoopStatement& self) { return &self.body; });

    py::class_<ForeverLoopStatement, Statement>(m, "ForeverLoopStatement")
        .def_property_readonly("body", [](const ForeverLoopStatement& self) { return &self.body; });

    py::class_<ExpressionStatement, Statement>(m, "ExpressionStatement")
        .def_property_readonly("expr", [](const ExpressionStatement& self) { return &self.expr; });

    py::class_<TimedStatement, Statement>(m, "TimedStatement")
        .def_property_readonly("timing", [](const TimedStatement& self) { return &self.timing; })
        .def_property_readonly("stmt", [](const TimedStatement& self) { return &self.stmt; });

    py::class_<ImmediateAssertionStatement, Statement>(m, "ImmediateAssertionStatement")
        .def_property_readonly("cond",
                               [](const ImmediateAssertionStatement& self) { return &self.cond; })
        .def_readonly("ifTrue", &ImmediateAssertionStatement::ifTrue)
        .def_readonly("ifFalse", &ImmediateAssertionStatement::ifFalse)
        .def_readonly("assertionKind", &ImmediateAssertionStatement::assertionKind)
        .def_readonly("isDeferred", &ImmediateAssertionStatement::isDeferred)
        .def_readonly("isFinal", &ImmediateAssertionStatement::isFinal);

    py::class_<ConcurrentAssertionStatement, Statement>(m, "ConcurrentAssertionStatement")
        .def_property_readonly("propertySpec",
                               [](const ConcurrentAssertionStatement& self) {
                                   return &self.propertySpec;
                               })
        .def_readonly("ifTrue", &ConcurrentAssertionStatement::ifTrue)
        .def_readonly("ifFalse", &ConcurrentAssertionStatement::ifFalse)
        .def_readonly("assertionKind", &ConcurrentAssertionStatement::assertionKind);

    py::class_<WaitStatement, Statement>(m, "WaitStatement")
        .def_property_readonly("cond", [](const WaitStatement& self) { return &self.cond; })
        .def_property_readonly("stmt", [](const WaitStatement& self) { return &self.stmt; });

    py::class_<WaitOrderStatement, Statement>(m, "WaitOrderStatement")
        .def_readonly("ifTrue", &WaitOrderStatement::ifTrue)
        .def_readonly("ifFalse", &WaitOrderStatement::ifFalse)
        .def_readonly("events", &WaitOrderStatement::events);

    py::class_<EventTriggerStatement, Statement>(m, "EventTriggerStatement")
        .def_property_readonly("target",
                               [](const EventTriggerStatement& self) { return &self.target; })
        .def_readonly("timing", &EventTriggerStatement::timing)
        .def_readonly("isNonBlocking", &EventTriggerStatement::isNonBlocking);

    py::class_<ProceduralAssignStatement, Statement>(m, "ProceduralAssignStatement")
        .def_property_readonly(
            "assignment", [](const ProceduralAssignStatement& self) { return &self.assignment; })
        .def_readonly("isForce", &ProceduralAssignStatement::isForce);

    py::class_<ProceduralDeassignStatement, Statement>(m, "ProceduralDeassignStatement")
        .def_property_readonly("lvalue",
                               [](const ProceduralDeassignStatement& self) { return &self.lvalue; })
        .def_readonly("isRelease", &ProceduralDeassignStatement::isRelease);

    py::class_<RandCaseStatement, Statement> randCaseStmt(m, "RandCaseStatement");
    randCaseStmt.def_readonly("items", &RandCaseStatement::items);

    py::class_<RandCaseStatement::Item>(randCaseStmt, "Item")
        .def_readonly("expr", &RandCaseStatement::Item::expr)
        .def_readonly("stmt", &RandCaseStatement::Item::stmt);

    py::class_<RandSequenceStatement, Statement>(m, "RandSequenceStatement")
        .def_readonly("firstProduction", &RandSequenceStatement::firstProduction);

    py::class_<ProceduralCheckerStatement, Statement>(m, "ProceduralCheckerStatement")
        .def_readonly("instances", &ProceduralCheckerStatement::instances);
}
