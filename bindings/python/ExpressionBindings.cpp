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

void registerExpressions(nb::module_& m) {
    EXPOSE_ENUM(m, ExpressionKind);
    EXPOSE_ENUM(m, UnaryOperator);
    EXPOSE_ENUM(m, BinaryOperator);
    EXPOSE_ENUM(m, RangeSelectionKind);
    EXPOSE_ENUM(m, ConversionKind);

    nb::class_<Expression>(m, "Expression")
        .def_ro("kind", &Expression::kind)
        .def_ro("type", &Expression::type)
        .def_ro("syntax", &Expression::syntax)
        .def_ro("sourceRange", &Expression::sourceRange)
        .def_prop_ro("constant", &Expression::getConstant)
        .def_prop_ro("bad", &Expression::bad)
        .def_prop_ro("isImplicitString", &Expression::isImplicitString)
        .def_prop_ro("isUnsizedInteger", &Expression::isUnsizedInteger)
        .def_prop_ro("effectiveWidth", &Expression::getEffectiveWidth)
        .def_prop_ro("hasHierarchicalReference", &Expression::hasHierarchicalReference)
        .def("eval", &Expression::eval, "context"_a)
        .def("evalLValue", &Expression::evalLValue, "context"_a)
        .def("isImplicitlyAssignableTo", &Expression::isImplicitlyAssignableTo, "compilation"_a,
             "type"_a)
        .def("getSymbolReference", &Expression::getSymbolReference, byrefint,
             "allowPacked"_a = true)
        .def("isEquivalentTo", &Expression::isEquivalentTo, "other"_a)
        .def("visit", &pyASTVisit<Expression>, "f"_a = nb::none(), "lookup_table"_a = nb::none(),
             PyASTVisitor::doc)
        .def("__repr__", [](const Expression& self) {
            return fmt::format("Expression(ExpressionKind.{})", toString(self.kind));
        });

    nb::class_<InvalidExpression, Expression>(m, "InvalidExpression");

    nb::class_<AssignmentExpression, Expression>(m, "AssignmentExpression")
        .def_ro("op", &AssignmentExpression::op)
        .def_ro("timingControl", &AssignmentExpression::timingControl)
        .def_prop_ro("isCompound", &AssignmentExpression::isCompound)
        .def_prop_ro("isNonBlocking", &AssignmentExpression::isNonBlocking)
        .def_prop_ro("isLValueArg", &AssignmentExpression::isLValueArg)
        .def_prop_ro("left", nb::overload_cast<>(&AssignmentExpression::left))
        .def_prop_ro("right", nb::overload_cast<>(&AssignmentExpression::right));

    nb::class_<ConversionExpression, Expression>(m, "ConversionExpression")
        .def_ro("conversionKind", &ConversionExpression::conversionKind)
        .def_ro("isConstCast", &ConversionExpression::isConstCast)
        .def_prop_ro("isImplicit", &ConversionExpression::isImplicit)
        .def_prop_ro("operand", nb::overload_cast<>(&ConversionExpression::operand));

    nb::class_<NewArrayExpression, Expression>(m, "NewArrayExpression")
        .def_prop_ro("sizeExpr", &NewArrayExpression::sizeExpr)
        .def_prop_ro("initExpr", &NewArrayExpression::initExpr);

    nb::class_<NewClassExpression, Expression>(m, "NewClassExpression")
        .def_ro("isSuperClass", &NewClassExpression::isSuperClass)
        .def_prop_ro("constructorCall", &NewClassExpression::constructorCall);

    nb::class_<NewCovergroupExpression, Expression>(m, "NewCovergroupExpression")
        .def_ro("arguments", &NewCovergroupExpression::arguments);

    nb::class_<AssignmentPatternExpressionBase, Expression>(m, "AssignmentPatternExpressionBase")
        .def_prop_ro("elements", &AssignmentPatternExpressionBase::elements);

    nb::class_<SimpleAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "SimpleAssignmentPatternExpression");

    nb::class_<StructuredAssignmentPatternExpression, AssignmentPatternExpressionBase> sape(
        m, "StructuredAssignmentPatternExpression");
    sape.def_ro("memberSetters", &StructuredAssignmentPatternExpression::memberSetters)
        .def_ro("typeSetters", &StructuredAssignmentPatternExpression::typeSetters)
        .def_ro("indexSetters", &StructuredAssignmentPatternExpression::indexSetters)
        .def_ro("defaultSetter", &StructuredAssignmentPatternExpression::defaultSetter);

    nb::class_<StructuredAssignmentPatternExpression::MemberSetter>(sape, "MemberSetter")
        .def_ro("member", &StructuredAssignmentPatternExpression::MemberSetter::member)
        .def_ro("expr", &StructuredAssignmentPatternExpression::MemberSetter::expr);

    nb::class_<StructuredAssignmentPatternExpression::TypeSetter>(sape, "TypeSetter")
        .def_ro("type", &StructuredAssignmentPatternExpression::TypeSetter::type)
        .def_ro("expr", &StructuredAssignmentPatternExpression::TypeSetter::expr);

    nb::class_<StructuredAssignmentPatternExpression::IndexSetter>(sape, "IndexSetter")
        .def_ro("index", &StructuredAssignmentPatternExpression::IndexSetter::index)
        .def_ro("expr", &StructuredAssignmentPatternExpression::IndexSetter::expr);

    nb::class_<ReplicatedAssignmentPatternExpression, AssignmentPatternExpressionBase>(
        m, "ReplicatedAssignmentPatternExpression")
        .def_prop_ro("count", &ReplicatedAssignmentPatternExpression::count);

    nb::class_<CallExpression, Expression> callExpr(m, "CallExpression");
    callExpr.def_ro("subroutine", &CallExpression::subroutine)
        .def_prop_ro("thisClass", &CallExpression::thisClass)
        .def_prop_ro("arguments", nb::overload_cast<>(&CallExpression::arguments))
        .def_prop_ro("isSystemCall", &CallExpression::isSystemCall)
        .def_prop_ro("subroutineName", &CallExpression::getSubroutineName)
        .def_prop_ro("subroutineKind", &CallExpression::getSubroutineKind);

    nb::class_<CallExpression::IteratorCallInfo>(callExpr, "IteratorCallInfo")
        .def_ro("iterExpr", &CallExpression::IteratorCallInfo::iterExpr)
        .def_ro("iterVar", &CallExpression::IteratorCallInfo::iterVar);

    nb::class_<CallExpression::RandomizeCallInfo>(callExpr, "RandomizeCallInfo")
        .def_ro("inlineConstraints", &CallExpression::RandomizeCallInfo::inlineConstraints)
        .def_ro("constraintRestrictions",
                &CallExpression::RandomizeCallInfo::constraintRestrictions);

    nb::class_<CallExpression::SystemCallInfo>(callExpr, "SystemCallInfo")
        .def_ro("subroutine", &CallExpression::SystemCallInfo::subroutine)
        .def_ro("scope", &CallExpression::SystemCallInfo::scope)
        .def_ro("extraInfo", &CallExpression::SystemCallInfo::extraInfo);

    nb::class_<IntegerLiteral, Expression>(m, "IntegerLiteral")
        .def_ro("isDeclaredUnsized", &IntegerLiteral::isDeclaredUnsized)
        .def_prop_ro("value", &IntegerLiteral::getValue);

    nb::class_<RealLiteral, Expression>(m, "RealLiteral")
        .def_prop_ro("value", &RealLiteral::getValue);

    nb::class_<TimeLiteral, Expression>(m, "TimeLiteral")
        .def_prop_ro("value", &TimeLiteral::getValue)
        .def_prop_ro("scale", &TimeLiteral::getScale);

    nb::class_<UnbasedUnsizedIntegerLiteral, Expression>(m, "UnbasedUnsizedIntegerLiteral")
        .def_prop_ro("literalValue", &UnbasedUnsizedIntegerLiteral::getLiteralValue)
        .def_prop_ro("value", &UnbasedUnsizedIntegerLiteral::getValue);

    nb::class_<NullLiteral, Expression>(m, "NullLiteral");
    nb::class_<UnboundedLiteral, Expression>(m, "UnboundedLiteral");

    nb::class_<StringLiteral, Expression>(m, "StringLiteral")
        .def_prop_ro("rawValue", &StringLiteral::getRawValue)
        .def_prop_ro("intValue", &StringLiteral::getIntValue)
        .def_prop_ro("value", &StringLiteral::getValue);

    nb::class_<ValueExpressionBase, Expression>(m, "ValueExpressionBase")
        .def_prop_ro("symbol", [](const ValueExpressionBase& self) { return &self.symbol; });

    nb::class_<NamedValueExpression, ValueExpressionBase>(m, "NamedValueExpression");
    nb::class_<HierarchicalValueExpression, ValueExpressionBase>(m, "HierarchicalValueExpression");
    nb::class_<DataTypeExpression, Expression>(m, "DataTypeExpression");
    nb::class_<LValueReferenceExpression, Expression>(m, "LValueReferenceExpression");
    nb::class_<EmptyArgumentExpression, Expression>(m, "EmptyArgumentExpression");

    nb::class_<TypeReferenceExpression, Expression>(m, "TypeReferenceExpression")
        .def_prop_ro("targetType",
                     [](const TypeReferenceExpression& self) { return &self.targetType; });

    nb::class_<ArbitrarySymbolExpression, Expression>(m, "ArbitrarySymbolExpression")
        .def_ro("symbol", &ArbitrarySymbolExpression::symbol);

    nb::class_<ClockingEventExpression, Expression>(m, "ClockingEventExpression")
        .def_prop_ro("timingControl",
                     [](const ClockingEventExpression& self) { return &self.timingControl; });

    nb::class_<AssertionInstanceExpression, Expression>(m, "AssertionInstanceExpression")
        .def_prop_ro("symbol", [](const AssertionInstanceExpression& self) { return &self.symbol; })
        .def_prop_ro("body", [](const AssertionInstanceExpression& self) { return &self.body; })
        .def_ro("arguments", &AssertionInstanceExpression::arguments)
        .def_ro("localVars", &AssertionInstanceExpression::localVars)
        .def_ro("isRecursiveProperty", &AssertionInstanceExpression::isRecursiveProperty);

    nb::class_<MinTypMaxExpression, Expression>(m, "MinTypMaxExpression")
        .def_prop_ro("min", nb::overload_cast<>(&MinTypMaxExpression::min))
        .def_prop_ro("typ", nb::overload_cast<>(&MinTypMaxExpression::typ))
        .def_prop_ro("max", nb::overload_cast<>(&MinTypMaxExpression::max))
        .def_prop_ro("selected", nb::overload_cast<>(&MinTypMaxExpression::selected));

    nb::class_<CopyClassExpression, Expression>(m, "CopyClassExpression")
        .def_prop_ro("sourceExpr", &CopyClassExpression::sourceExpr);

    nb::class_<DistExpression, Expression> distExpr(m, "DistExpression");
    distExpr.def_prop_ro("left", &DistExpression::left)
        .def_prop_ro("items", &DistExpression::items)
        .def_prop_ro("defaultWeight", &DistExpression::defaultWeight);

    nb::class_<DistExpression::DistWeight> distWeight(distExpr, "DistWeight");
    distWeight.def_ro("kind", &DistExpression::DistWeight::kind)
        .def_prop_ro("expr", [](const DistExpression::DistWeight& self) { return self.expr; });

    nb::enum_<DistExpression::DistWeight::Kind>(distWeight, "Kind")
        .value("PerValue", DistExpression::DistWeight::PerValue)
        .value("PerRange", DistExpression::DistWeight::PerRange)
        .export_values();

    nb::class_<DistExpression::DistItem>(distExpr, "DistItem")
        .def_ro("weight", &DistExpression::DistItem::weight)
        .def_prop_ro("value", [](const DistExpression::DistItem& self) { return &self.value; });

    nb::class_<TaggedUnionExpression, Expression>(m, "TaggedUnionExpression")
        .def_prop_ro("member", [](const TaggedUnionExpression& self) { return &self.member; })
        .def_ro("valueExpr", &TaggedUnionExpression::valueExpr);

    nb::class_<UnaryExpression, Expression>(m, "UnaryExpression")
        .def_prop_ro("operand", nb::overload_cast<>(&UnaryExpression::operand))
        .def_ro("op", &UnaryExpression::op);

    nb::class_<BinaryExpression, Expression>(m, "BinaryExpression")
        .def_prop_ro("left", nb::overload_cast<>(&BinaryExpression::left))
        .def_prop_ro("right", nb::overload_cast<>(&BinaryExpression::right))
        .def_ro("op", &BinaryExpression::op);

    nb::class_<ConditionalExpression, Expression> condExpr(m, "ConditionalExpression");
    condExpr.def_prop_ro("left", nb::overload_cast<>(&ConditionalExpression::left))
        .def_prop_ro("right", nb::overload_cast<>(&ConditionalExpression::right))
        .def_ro("conditions", &ConditionalExpression::conditions);

    nb::class_<ConditionalExpression::Condition>(condExpr, "Condition")
        .def_ro("expr", &ConditionalExpression::Condition::expr)
        .def_ro("pattern", &ConditionalExpression::Condition::pattern);

    nb::class_<InsideExpression, Expression>(m, "InsideExpression")
        .def_prop_ro("left", &InsideExpression::left)
        .def_prop_ro("rangeList", &InsideExpression::rangeList);

    nb::class_<ConcatenationExpression, Expression>(m, "ConcatenationExpression")
        .def_prop_ro("operands", nb::overload_cast<>(&ConcatenationExpression::operands));

    nb::class_<ReplicationExpression, Expression>(m, "ReplicationExpression")
        .def_prop_ro("count", &ReplicationExpression::count)
        .def_prop_ro("concat", nb::overload_cast<>(&ReplicationExpression::concat));

    nb::class_<StreamingConcatenationExpression, Expression> streamConcatExpr(
        m, "StreamingConcatenationExpression");
    streamConcatExpr.def_prop_ro("sliceSize", &StreamingConcatenationExpression::getSliceSize)
        .def_prop_ro("isFixedSize", &StreamingConcatenationExpression::isFixedSize)
        .def_prop_ro("bitstreamWidth", &StreamingConcatenationExpression::getBitstreamWidth)
        .def_prop_ro("streams", &StreamingConcatenationExpression::streams);

    nb::class_<StreamingConcatenationExpression::StreamExpression>(streamConcatExpr,
                                                                   "StreamExpression")
        .def_ro("operand", &StreamingConcatenationExpression::StreamExpression::operand)
        .def_ro("withExpr", &StreamingConcatenationExpression::StreamExpression::withExpr)
        .def_ro("constantWithWidth",
                &StreamingConcatenationExpression::StreamExpression::constantWithWidth);

    nb::class_<ValueRangeExpression, Expression>(m, "ValueRangeExpression")
        .def_prop_ro("left", nb::overload_cast<>(&ValueRangeExpression::left))
        .def_prop_ro("right", nb::overload_cast<>(&ValueRangeExpression::right));

    nb::class_<ElementSelectExpression, Expression>(m, "ElementSelectExpression")
        .def_prop_ro("value", nb::overload_cast<>(&ElementSelectExpression::value))
        .def_prop_ro("selector", &ElementSelectExpression::selector);

    nb::class_<RangeSelectExpression, Expression>(m, "RangeSelectExpression")
        .def_prop_ro("selectionKind", &RangeSelectExpression::getSelectionKind)
        .def_prop_ro("value", nb::overload_cast<>(&RangeSelectExpression::value))
        .def_prop_ro("left", &RangeSelectExpression::left)
        .def_prop_ro("right", &RangeSelectExpression::right);

    nb::class_<MemberAccessExpression, Expression>(m, "MemberAccessExpression")
        .def_prop_ro("value", nb::overload_cast<>(&MemberAccessExpression::value))
        .def_prop_ro("member", [](const MemberAccessExpression& self) { return &self.member; });
}
