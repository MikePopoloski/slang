//------------------------------------------------------------------------------
// binding.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/AllSyntax.h"

void registerBinding(py::module_& m) {
    EXPOSE_ENUM(m, ExpressionKind);
    EXPOSE_ENUM(m, UnaryOperator);
    EXPOSE_ENUM(m, BinaryOperator);
    EXPOSE_ENUM(m, RangeSelectionKind);
    EXPOSE_ENUM(m, ConversionKind);
    EXPOSE_ENUM(m, StatementKind);
    EXPOSE_ENUM(m, CaseStatementCondition);
    EXPOSE_ENUM(m, CaseStatementCheck);

    py::class_<Expression>(m, "Expression")
        .def_readonly("kind", &Expression::kind)
        .def_readonly("type", &Expression::type)
        .def_readonly("constant", &Expression::constant)
        .def_readonly("syntax", &Expression::syntax)
        .def_readonly("sourceRange", &Expression::sourceRange)
        .def_property_readonly("bad", &Expression::bad)
        .def_property_readonly("isImplicitString", &Expression::isImplicitString)
        .def_property_readonly("isUnsizedInteger", &Expression::isUnsizedInteger)
        .def_property_readonly("effectiveWidth", &Expression::getEffectiveWidth)
        .def_property_readonly("hasHierarchicalReference", &Expression::hasHierarchicalReference)
        .def("eval", &Expression::eval)
        .def("evalLValue", &Expression::evalLValue)
        .def("canConnectToRefArg", &Expression::canConnectToRefArg)
        .def("isImplicitlyAssignableTo", &Expression::isImplicitlyAssignableTo)
        .def("getSymbolReference", &Expression::getSymbolReference)
        .def("__repr__", [](const Expression& self) {
            return fmt::format("Expression(ExpressionKind.{})", toString(self.kind));
        });

    py::class_<InvalidExpression, Expression>(m, "InvalidExpression");

    py::class_<AssignmentExpression, Expression>(m, "AssignmentExpression")
        .def_readonly("op", &AssignmentExpression::op)
        .def_readonly("timingControl", &AssignmentExpression::timingControl)
        .def_property_readonly("isCompound", &AssignmentExpression::isCompound)
        .def_property_readonly("isNonBlocking", &AssignmentExpression::isNonBlocking)
        .def_property_readonly("isLValueArg", &AssignmentExpression::isLValueArg)
        .def_property_readonly("left", py::overload_cast<>(&AssignmentExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&AssignmentExpression::right));

    py::class_<ConversionExpression, Expression>(m, "ConversionExpression")
        .def_readonly("conversionKind", &ConversionExpression::conversionKind)
        .def_property_readonly("isImplicit", &ConversionExpression::isImplicit)
        .def_property_readonly("operand", py::overload_cast<>(&ConversionExpression::operand));

    py::class_<NewArrayExpression, Expression>(m, "NewArrayExpression")
        .def_property_readonly("sizeExpr", &NewArrayExpression::sizeExpr)
        .def_property_readonly("initExpr", &NewArrayExpression::initExpr);

    py::class_<NewClassExpression, Expression>(m, "NewClassExpression")
        .def_readonly("isSuperClass", &NewClassExpression::isSuperClass)
        .def_property_readonly("constructorCall", &NewClassExpression::constructorCall);

    py::class_<NewCovergroupExpression, Expression>(m, "NewCovergroupExpression")
        .def_readonly("arguments", &NewCovergroupExpression::arguments);

    py::class_<AssignmentPatternExpressionBase, Expression>(m, "AssignmentPatternExpressionBase")
        .def_property_readonly("elements", &AssignmentPatternExpressionBase::elements);

    py::class_<SimpleAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "SimpleAssignmentPatternExpression");

    py::class_<StructuredAssignmentPatternExpression, AssignmentPatternExpressionBase> sape(
        m, "StructuredAssignmentPatternExpression");
    sape.def_readonly("memberSetters", &StructuredAssignmentPatternExpression::memberSetters)
        .def_readonly("typeSetters", &StructuredAssignmentPatternExpression::typeSetters)
        .def_readonly("indexSetters", &StructuredAssignmentPatternExpression::indexSetters)
        .def_readonly("defaultSetter", &StructuredAssignmentPatternExpression::defaultSetter);

    py::class_<StructuredAssignmentPatternExpression::MemberSetter>(sape, "MemberSetter")
        .def_readonly("member", &StructuredAssignmentPatternExpression::MemberSetter::member)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::MemberSetter::expr);

    py::class_<StructuredAssignmentPatternExpression::TypeSetter>(sape, "TypeSetter")
        .def_readonly("type", &StructuredAssignmentPatternExpression::TypeSetter::type)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::TypeSetter::expr);

    py::class_<StructuredAssignmentPatternExpression::IndexSetter>(sape, "IndexSetter")
        .def_readonly("index", &StructuredAssignmentPatternExpression::IndexSetter::index)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::IndexSetter::expr);

    py::class_<ReplicatedAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "ReplicatedAssignmentPatternExpression")
        .def_property_readonly("count", &ReplicatedAssignmentPatternExpression::count);

    py::class_<CallExpression, Expression> callExpr(m, "CallExpression");
    callExpr.def_readonly("subroutine", &CallExpression::subroutine)
        .def_property_readonly("thisClass", &CallExpression::thisClass)
        .def_property_readonly("arguments", py::overload_cast<>(&CallExpression::arguments))
        .def_property_readonly("isSystemCall", &CallExpression::isSystemCall)
        .def_property_readonly("subroutineName", &CallExpression::getSubroutineName)
        .def_property_readonly("subroutineKind", &CallExpression::getSubroutineKind);

    py::class_<CallExpression::IteratorCallInfo>(callExpr, "IteratorCallInfo")
        .def_readonly("iterExpr", &CallExpression::IteratorCallInfo::iterExpr)
        .def_readonly("iterVar", &CallExpression::IteratorCallInfo::iterVar);

    py::class_<CallExpression::RandomizeCallInfo>(callExpr, "RandomizeCallInfo")
        .def_readonly("inlineConstraints", &CallExpression::RandomizeCallInfo::inlineConstraints)
        .def_readonly("constraintRestrictions",
                      &CallExpression::RandomizeCallInfo::constraintRestrictions);

    py::class_<CallExpression::SystemCallInfo>(callExpr, "SystemCallInfo")
        .def_readonly("subroutine", &CallExpression::SystemCallInfo::subroutine)
        .def_readonly("scope", &CallExpression::SystemCallInfo::scope)
        .def_readonly("extraInfo", &CallExpression::SystemCallInfo::extraInfo);

    py::class_<IntegerLiteral, Expression>(m, "IntegerLiteral")
        .def_readonly("isDeclaredUnsized", &IntegerLiteral::isDeclaredUnsized)
        .def_property_readonly("value", &IntegerLiteral::getValue);

    py::class_<RealLiteral, Expression>(m, "RealLiteral")
        .def_property_readonly("value", &RealLiteral::getValue);

    py::class_<TimeLiteral, Expression>(m, "TimeLiteral")
        .def_property_readonly("value", &TimeLiteral::getValue);

    py::class_<UnbasedUnsizedIntegerLiteral, Expression>(m, "UnbasedUnsizedIntegerLiteral")
        .def_property_readonly("literalValue", &UnbasedUnsizedIntegerLiteral::getLiteralValue)
        .def_property_readonly("value", &UnbasedUnsizedIntegerLiteral::getValue);

    py::class_<NullLiteral, Expression>(m, "NullLiteral");
    py::class_<UnboundedLiteral, Expression>(m, "UnboundedLiteral");

    py::class_<StringLiteral, Expression>(m, "StringLiteral")
        .def_property_readonly("rawValue", &StringLiteral::getRawValue)
        .def_property_readonly("intValue", &StringLiteral::getIntValue)
        .def_property_readonly("value", &StringLiteral::getValue);

    py::class_<ValueExpressionBase, Expression>(m, "ValueExpressionBase")
        .def_property_readonly("symbol",
                               [](const ValueExpressionBase& self) { return &self.symbol; });

    py::class_<NamedValueExpression, ValueExpressionBase>(m, "NamedValueExpression");
    py::class_<HierarchicalValueExpression, ValueExpressionBase>(m, "HierarchicalValueExpression");
    py::class_<DataTypeExpression, Expression>(m, "DataTypeExpression");
    py::class_<LValueReferenceExpression, Expression>(m, "LValueReferenceExpression");
    py::class_<EmptyArgumentExpression, Expression>(m, "EmptyArgumentExpression");

    py::class_<TypeReferenceExpression, Expression>(m, "TypeReferenceExpression")
        .def_property_readonly(
            "targetType", [](const TypeReferenceExpression& self) { return &self.targetType; });

    py::class_<HierarchicalReferenceExpression, Expression>(m, "HierarchicalReferenceExpression")
        .def_readonly("symbol", &HierarchicalReferenceExpression::symbol);

    py::class_<ClockingEventExpression, Expression>(m, "ClockingEventExpression")
        .def_property_readonly("timingControl", [](const ClockingEventExpression& self) {
            return &self.timingControl;
        });

    py::class_<AssertionInstanceExpression, Expression>(m, "AssertionInstanceExpression")
        .def_property_readonly("symbol",
                               [](const AssertionInstanceExpression& self) { return &self.symbol; })
        .def_property_readonly("body",
                               [](const AssertionInstanceExpression& self) { return &self.body; })
        .def_readonly("arguments", &AssertionInstanceExpression::arguments)
        .def_readonly("localVars", &AssertionInstanceExpression::localVars)
        .def_readonly("isRecursiveProperty", &AssertionInstanceExpression::isRecursiveProperty);

    py::class_<MinTypMaxExpression, Expression>(m, "MinTypMaxExpression")
        .def_property_readonly("min", py::overload_cast<>(&MinTypMaxExpression::min))
        .def_property_readonly("typ", py::overload_cast<>(&MinTypMaxExpression::typ))
        .def_property_readonly("max", py::overload_cast<>(&MinTypMaxExpression::max))
        .def_property_readonly("selected", py::overload_cast<>(&MinTypMaxExpression::selected));

    py::class_<CopyClassExpression, Expression>(m, "CopyClassExpression")
        .def_property_readonly("sourceExpr", &CopyClassExpression::sourceExpr);

    py::class_<DistExpression, Expression> distExpr(m, "DistExpression");
    distExpr.def_property_readonly("left", &DistExpression::left)
        .def_property_readonly("items", &DistExpression::items);

    py::class_<DistExpression::DistWeight> distWeight(distExpr, "DistWeight");
    distWeight.def_readonly("kind", &DistExpression::DistWeight::kind)
        .def_property_readonly("expr",
                               [](const DistExpression::DistWeight& self) { return &self.expr; });

    py::enum_<DistExpression::DistWeight::Kind>(distWeight, "Kind")
        .value("PerValue", DistExpression::DistWeight::PerValue)
        .value("PerRange", DistExpression::DistWeight::PerRange)
        .export_values();

    py::class_<DistExpression::DistItem>(distExpr, "DistItem")
        .def_readonly("weight", &DistExpression::DistItem::weight)
        .def_property_readonly("value",
                               [](const DistExpression::DistItem& self) { return &self.value; });

    py::class_<TaggedUnionExpression, Expression>(m, "TaggedUnionExpression")
        .def_property_readonly("member",
                               [](const TaggedUnionExpression& self) { return &self.member; })
        .def_readonly("valueExpr", &TaggedUnionExpression::valueExpr);

    py::class_<UnaryExpression, Expression>(m, "UnaryExpression")
        .def_property_readonly("operand", py::overload_cast<>(&UnaryExpression::operand))
        .def_readonly("op", &UnaryExpression::op);

    py::class_<BinaryExpression, Expression>(m, "BinaryExpression")
        .def_property_readonly("left", py::overload_cast<>(&BinaryExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&BinaryExpression::right))
        .def_readonly("op", &BinaryExpression::op);

    py::class_<ConditionalExpression, Expression> condExpr(m, "ConditionalExpression");
    condExpr.def_property_readonly("left", py::overload_cast<>(&ConditionalExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&ConditionalExpression::right))
        .def_readonly("conditions", &ConditionalExpression::conditions);

    py::class_<ConditionalExpression::Condition>(condExpr, "Condition")
        .def_readonly("expr", &ConditionalExpression::Condition::expr)
        .def_readonly("pattern", &ConditionalExpression::Condition::pattern);

    py::class_<InsideExpression, Expression>(m, "InsideExpression")
        .def_property_readonly("left", &InsideExpression::left)
        .def_property_readonly("rangeList", &InsideExpression::rangeList);

    py::class_<ConcatenationExpression, Expression>(m, "ConcatenationExpression")
        .def_property_readonly("operands", &ConcatenationExpression::operands);

    py::class_<ReplicationExpression, Expression>(m, "ReplicationExpression")
        .def_property_readonly("count", &ReplicationExpression::count)
        .def_property_readonly("concat", py::overload_cast<>(&ReplicationExpression::concat));

    // TODO:
    // py::class_<StreamingConcatenationExpression, Expression>(m,
    // "StreamingConcatenationExpression")

    py::class_<OpenRangeExpression, Expression>(m, "OpenRangeExpression")
        .def_property_readonly("left", py::overload_cast<>(&OpenRangeExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&OpenRangeExpression::right));

    py::class_<ElementSelectExpression, Expression>(m, "ElementSelectExpression")
        .def_property_readonly("value", py::overload_cast<>(&ElementSelectExpression::value))
        .def_property_readonly("selector", &ElementSelectExpression::selector);

    py::class_<RangeSelectExpression, Expression>(m, "RangeSelectExpression")
        .def_readonly("selectionKind", &RangeSelectExpression::selectionKind)
        .def_property_readonly("value", py::overload_cast<>(&RangeSelectExpression::value))
        .def_property_readonly("left", &RangeSelectExpression::left)
        .def_property_readonly("right", &RangeSelectExpression::right);

    py::class_<MemberAccessExpression, Expression>(m, "MemberAccessExpression")
        .def_readonly("offset", &MemberAccessExpression::offset)
        .def_property_readonly("value", py::overload_cast<>(&MemberAccessExpression::value))
        .def_property_readonly("member",
                               [](const MemberAccessExpression& self) { return &self.member; });

    py::class_<Statement> stmt(m, "Statement");
    stmt.def_readonly("kind", &Statement::kind)
        .def_readonly("syntax", &Statement::syntax)
        .def_readonly("sourceRange", &Statement::sourceRange)
        .def_property_readonly("bad", &Statement::bad)
        .def("eval", &Statement::eval)
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
        .def_readonly("isHierarchical", &DisableStatement::isHierarchical)
        .def_property_readonly("target", [](const DisableStatement& self) { return &self.target; });

    py::class_<VariableDeclStatement, Statement>(m, "VariableDeclStatement")
        .def_property_readonly("symbol",
                               [](const VariableDeclStatement& self) { return &self.symbol; });

    py::class_<ConditionalStatement, Statement> condStmt(m, "ConditionalStatement");
    condStmt.def_readonly("conditions", &ConditionalStatement::conditions)
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
        .def_property_readonly(
            "propertySpec",
            [](const ConcurrentAssertionStatement& self) { return &self.propertySpec; })
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
}
