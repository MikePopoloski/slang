//------------------------------------------------------------------------------
// ExpressionBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/syntax/AllSyntax.h"

void registerExpressions(py::module_& m) {
    EXPOSE_ENUM(m, ExpressionKind);
    EXPOSE_ENUM(m, UnaryOperator);
    EXPOSE_ENUM(m, BinaryOperator);
    EXPOSE_ENUM(m, RangeSelectionKind);
    EXPOSE_ENUM(m, ConversionKind);

    py::classh<Expression>(m, "Expression")
        .def_readonly("kind", &Expression::kind)
        .def_readonly("type", &Expression::type)
        .def_readonly("syntax", &Expression::syntax)
        .def_readonly("sourceRange", &Expression::sourceRange)
        .def_property_readonly("constant", &Expression::getConstant)
        .def_property_readonly("bad", &Expression::bad)
        .def_property_readonly("isImplicitString", &Expression::isImplicitString)
        .def_property_readonly("isUnsizedInteger", &Expression::isUnsizedInteger)
        .def_property_readonly("effectiveWidth", &Expression::getEffectiveWidth)
        .def_property_readonly("hasHierarchicalReference", &Expression::hasHierarchicalReference)
        .def("eval", &Expression::eval, "context"_a)
        .def("evalLValue", &Expression::evalLValue, "context"_a)
        .def("isImplicitlyAssignableTo", &Expression::isImplicitlyAssignableTo, "compilation"_a,
             "type"_a)
        .def("getSymbolReference", &Expression::getSymbolReference, byrefint,
             "allowPacked"_a = true)
        .def("isEquivalentTo", &Expression::isEquivalentTo, "other"_a)
        .def("visit", &pyASTVisit<Expression>, "f"_a, PyASTVisitor::doc)
        .def("__repr__", [](const Expression& self) {
            return fmt::format("Expression(ExpressionKind.{})", toString(self.kind));
        });

    py::classh<InvalidExpression, Expression>(m, "InvalidExpression");

    py::classh<AssignmentExpression, Expression>(m, "AssignmentExpression")
        .def_readonly("op", &AssignmentExpression::op)
        .def_readonly("timingControl", &AssignmentExpression::timingControl)
        .def_property_readonly("isCompound", &AssignmentExpression::isCompound)
        .def_property_readonly("isNonBlocking", &AssignmentExpression::isNonBlocking)
        .def_property_readonly("isLValueArg", &AssignmentExpression::isLValueArg)
        .def_property_readonly("left", py::overload_cast<>(&AssignmentExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&AssignmentExpression::right));

    py::classh<ConversionExpression, Expression>(m, "ConversionExpression")
        .def_readonly("conversionKind", &ConversionExpression::conversionKind)
        .def_readonly("isConstCast", &ConversionExpression::isConstCast)
        .def_property_readonly("isImplicit", &ConversionExpression::isImplicit)
        .def_property_readonly("operand", py::overload_cast<>(&ConversionExpression::operand));

    py::classh<NewArrayExpression, Expression>(m, "NewArrayExpression")
        .def_property_readonly("sizeExpr", &NewArrayExpression::sizeExpr)
        .def_property_readonly("initExpr", &NewArrayExpression::initExpr);

    py::classh<NewClassExpression, Expression>(m, "NewClassExpression")
        .def_readonly("isSuperClass", &NewClassExpression::isSuperClass)
        .def_property_readonly("constructorCall", &NewClassExpression::constructorCall);

    py::classh<NewCovergroupExpression, Expression>(m, "NewCovergroupExpression")
        .def_readonly("arguments", &NewCovergroupExpression::arguments);

    py::classh<AssignmentPatternExpressionBase, Expression>(m, "AssignmentPatternExpressionBase")
        .def_property_readonly("elements", &AssignmentPatternExpressionBase::elements);

    py::classh<SimpleAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "SimpleAssignmentPatternExpression");

    py::classh<StructuredAssignmentPatternExpression, AssignmentPatternExpressionBase> sape(
        m, "StructuredAssignmentPatternExpression");
    sape.def_readonly("memberSetters", &StructuredAssignmentPatternExpression::memberSetters)
        .def_readonly("typeSetters", &StructuredAssignmentPatternExpression::typeSetters)
        .def_readonly("indexSetters", &StructuredAssignmentPatternExpression::indexSetters)
        .def_readonly("defaultSetter", &StructuredAssignmentPatternExpression::defaultSetter);

    py::classh<StructuredAssignmentPatternExpression::MemberSetter>(sape, "MemberSetter")
        .def_readonly("member", &StructuredAssignmentPatternExpression::MemberSetter::member)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::MemberSetter::expr);

    py::classh<StructuredAssignmentPatternExpression::TypeSetter>(sape, "TypeSetter")
        .def_readonly("type", &StructuredAssignmentPatternExpression::TypeSetter::type)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::TypeSetter::expr);

    py::classh<StructuredAssignmentPatternExpression::IndexSetter>(sape, "IndexSetter")
        .def_readonly("index", &StructuredAssignmentPatternExpression::IndexSetter::index)
        .def_readonly("expr", &StructuredAssignmentPatternExpression::IndexSetter::expr);

    py::classh<ReplicatedAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "ReplicatedAssignmentPatternExpression")
        .def_property_readonly("count", &ReplicatedAssignmentPatternExpression::count);

    py::classh<CallExpression, Expression> callExpr(m, "CallExpression");
    callExpr.def_readonly("subroutine", &CallExpression::subroutine)
        .def_property_readonly("thisClass", &CallExpression::thisClass)
        .def_property_readonly("arguments", py::overload_cast<>(&CallExpression::arguments))
        .def_property_readonly("isSystemCall", &CallExpression::isSystemCall)
        .def_property_readonly("subroutineName", &CallExpression::getSubroutineName)
        .def_property_readonly("subroutineKind", &CallExpression::getSubroutineKind);

    py::classh<CallExpression::IteratorCallInfo>(callExpr, "IteratorCallInfo")
        .def_readonly("iterExpr", &CallExpression::IteratorCallInfo::iterExpr)
        .def_readonly("iterVar", &CallExpression::IteratorCallInfo::iterVar);

    py::classh<CallExpression::RandomizeCallInfo>(callExpr, "RandomizeCallInfo")
        .def_readonly("inlineConstraints", &CallExpression::RandomizeCallInfo::inlineConstraints)
        .def_readonly("constraintRestrictions",
                      &CallExpression::RandomizeCallInfo::constraintRestrictions);

    py::classh<CallExpression::SystemCallInfo>(callExpr, "SystemCallInfo")
        .def_readonly("subroutine", &CallExpression::SystemCallInfo::subroutine)
        .def_readonly("scope", &CallExpression::SystemCallInfo::scope)
        .def_readonly("extraInfo", &CallExpression::SystemCallInfo::extraInfo);

    py::classh<IntegerLiteral, Expression>(m, "IntegerLiteral")
        .def_readonly("isDeclaredUnsized", &IntegerLiteral::isDeclaredUnsized)
        .def_property_readonly("value", &IntegerLiteral::getValue);

    py::classh<RealLiteral, Expression>(m, "RealLiteral")
        .def_property_readonly("value", &RealLiteral::getValue);

    py::classh<TimeLiteral, Expression>(m, "TimeLiteral")
        .def_property_readonly("value", &TimeLiteral::getValue)
        .def_property_readonly("scale", &TimeLiteral::getScale);

    py::classh<UnbasedUnsizedIntegerLiteral, Expression>(m, "UnbasedUnsizedIntegerLiteral")
        .def_property_readonly("literalValue", &UnbasedUnsizedIntegerLiteral::getLiteralValue)
        .def_property_readonly("value", &UnbasedUnsizedIntegerLiteral::getValue);

    py::classh<NullLiteral, Expression>(m, "NullLiteral");
    py::classh<UnboundedLiteral, Expression>(m, "UnboundedLiteral");

    py::classh<StringLiteral, Expression>(m, "StringLiteral")
        .def_property_readonly("rawValue", &StringLiteral::getRawValue)
        .def_property_readonly("intValue", &StringLiteral::getIntValue)
        .def_property_readonly("value", &StringLiteral::getValue);

    py::classh<ValueExpressionBase, Expression>(m, "ValueExpressionBase")
        .def_property_readonly("symbol",
                               [](const ValueExpressionBase& self) { return &self.symbol; });

    py::classh<NamedValueExpression, ValueExpressionBase>(m, "NamedValueExpression");
    py::classh<HierarchicalValueExpression, ValueExpressionBase>(m, "HierarchicalValueExpression");
    py::classh<DataTypeExpression, Expression>(m, "DataTypeExpression");
    py::classh<LValueReferenceExpression, Expression>(m, "LValueReferenceExpression");
    py::classh<EmptyArgumentExpression, Expression>(m, "EmptyArgumentExpression");

    py::classh<TypeReferenceExpression, Expression>(m, "TypeReferenceExpression")
        .def_property_readonly("targetType", [](const TypeReferenceExpression& self) {
            return &self.targetType;
        });

    py::classh<ArbitrarySymbolExpression, Expression>(m, "ArbitrarySymbolExpression")
        .def_readonly("symbol", &ArbitrarySymbolExpression::symbol);

    py::classh<ClockingEventExpression, Expression>(m, "ClockingEventExpression")
        .def_property_readonly("timingControl", [](const ClockingEventExpression& self) {
            return &self.timingControl;
        });

    py::classh<AssertionInstanceExpression, Expression>(m, "AssertionInstanceExpression")
        .def_property_readonly("symbol",
                               [](const AssertionInstanceExpression& self) { return &self.symbol; })
        .def_property_readonly("body",
                               [](const AssertionInstanceExpression& self) { return &self.body; })
        .def_readonly("arguments", &AssertionInstanceExpression::arguments)
        .def_readonly("localVars", &AssertionInstanceExpression::localVars)
        .def_readonly("isRecursiveProperty", &AssertionInstanceExpression::isRecursiveProperty);

    py::classh<MinTypMaxExpression, Expression>(m, "MinTypMaxExpression")
        .def_property_readonly("min", py::overload_cast<>(&MinTypMaxExpression::min))
        .def_property_readonly("typ", py::overload_cast<>(&MinTypMaxExpression::typ))
        .def_property_readonly("max", py::overload_cast<>(&MinTypMaxExpression::max))
        .def_property_readonly("selected", py::overload_cast<>(&MinTypMaxExpression::selected));

    py::classh<CopyClassExpression, Expression>(m, "CopyClassExpression")
        .def_property_readonly("sourceExpr", &CopyClassExpression::sourceExpr);

    py::classh<DistExpression, Expression> distExpr(m, "DistExpression");
    distExpr.def_property_readonly("left", &DistExpression::left)
        .def_property_readonly("items", &DistExpression::items)
        .def_property_readonly("defaultWeight", &DistExpression::defaultWeight);

    py::classh<DistExpression::DistWeight> distWeight(distExpr, "DistWeight");
    distWeight.def_readonly("kind", &DistExpression::DistWeight::kind)
        .def_property_readonly("expr",
                               [](const DistExpression::DistWeight& self) { return self.expr; });

    py::native_enum<DistExpression::DistWeight::Kind>(distWeight, "Kind", "enum.Enum")
        .value("PerValue", DistExpression::DistWeight::PerValue)
        .value("PerRange", DistExpression::DistWeight::PerRange)
        .export_values()
        .finalize();

    py::classh<DistExpression::DistItem>(distExpr, "DistItem")
        .def_readonly("weight", &DistExpression::DistItem::weight)
        .def_property_readonly("value",
                               [](const DistExpression::DistItem& self) { return &self.value; });

    py::classh<TaggedUnionExpression, Expression>(m, "TaggedUnionExpression")
        .def_property_readonly("member",
                               [](const TaggedUnionExpression& self) { return &self.member; })
        .def_readonly("valueExpr", &TaggedUnionExpression::valueExpr);

    py::classh<UnaryExpression, Expression>(m, "UnaryExpression")
        .def_property_readonly("operand", py::overload_cast<>(&UnaryExpression::operand))
        .def_readonly("op", &UnaryExpression::op);

    py::classh<BinaryExpression, Expression>(m, "BinaryExpression")
        .def_property_readonly("left", py::overload_cast<>(&BinaryExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&BinaryExpression::right))
        .def_readonly("op", &BinaryExpression::op);

    py::classh<ConditionalExpression, Expression> condExpr(m, "ConditionalExpression");
    condExpr.def_property_readonly("left", py::overload_cast<>(&ConditionalExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&ConditionalExpression::right))
        .def_readonly("conditions", &ConditionalExpression::conditions);

    py::classh<ConditionalExpression::Condition>(condExpr, "Condition")
        .def_readonly("expr", &ConditionalExpression::Condition::expr)
        .def_readonly("pattern", &ConditionalExpression::Condition::pattern);

    py::classh<InsideExpression, Expression>(m, "InsideExpression")
        .def_property_readonly("left", &InsideExpression::left)
        .def_property_readonly("rangeList", &InsideExpression::rangeList);

    py::classh<ConcatenationExpression, Expression>(m, "ConcatenationExpression")
        .def_property_readonly("operands", py::overload_cast<>(&ConcatenationExpression::operands));

    py::classh<ReplicationExpression, Expression>(m, "ReplicationExpression")
        .def_property_readonly("count", &ReplicationExpression::count)
        .def_property_readonly("concat", py::overload_cast<>(&ReplicationExpression::concat));

    py::classh<StreamingConcatenationExpression, Expression> streamConcatExpr(
        m, "StreamingConcatenationExpression");
    streamConcatExpr
        .def_property_readonly("sliceSize", &StreamingConcatenationExpression::getSliceSize)
        .def_property_readonly("isFixedSize", &StreamingConcatenationExpression::isFixedSize)
        .def_property_readonly("bitstreamWidth",
                               &StreamingConcatenationExpression::getBitstreamWidth)
        .def_property_readonly("streams", &StreamingConcatenationExpression::streams);

    py::classh<StreamingConcatenationExpression::StreamExpression>(streamConcatExpr,
                                                                   "StreamExpression")
        .def_readonly("operand", &StreamingConcatenationExpression::StreamExpression::operand)
        .def_readonly("withExpr", &StreamingConcatenationExpression::StreamExpression::withExpr)
        .def_readonly("constantWithWidth",
                      &StreamingConcatenationExpression::StreamExpression::constantWithWidth);

    py::classh<ValueRangeExpression, Expression>(m, "ValueRangeExpression")
        .def_property_readonly("left", py::overload_cast<>(&ValueRangeExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&ValueRangeExpression::right));

    py::classh<ElementSelectExpression, Expression>(m, "ElementSelectExpression")
        .def_property_readonly("value", py::overload_cast<>(&ElementSelectExpression::value))
        .def_property_readonly("selector", &ElementSelectExpression::selector);

    py::classh<RangeSelectExpression, Expression>(m, "RangeSelectExpression")
        .def_property_readonly("selectionKind", &RangeSelectExpression::getSelectionKind)
        .def_property_readonly("value", py::overload_cast<>(&RangeSelectExpression::value))
        .def_property_readonly("left", &RangeSelectExpression::left)
        .def_property_readonly("right", &RangeSelectExpression::right);

    py::classh<MemberAccessExpression, Expression>(m, "MemberAccessExpression")
        .def_property_readonly("value", py::overload_cast<>(&MemberAccessExpression::value))
        .def_property_readonly("member",
                               [](const MemberAccessExpression& self) { return &self.member; });
}
