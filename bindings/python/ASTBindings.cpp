//------------------------------------------------------------------------------
// ASTBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/syntax/AllSyntax.h"

void registerAST(py::module_& m) {
    EXPOSE_ENUM(m, ExpressionKind);
    EXPOSE_ENUM(m, UnaryOperator);
    EXPOSE_ENUM(m, BinaryOperator);
    EXPOSE_ENUM(m, RangeSelectionKind);
    EXPOSE_ENUM(m, ConversionKind);
    EXPOSE_ENUM(m, StatementKind);
    EXPOSE_ENUM(m, CaseStatementCondition);
    EXPOSE_ENUM(m, UniquePriorityCheck);
    EXPOSE_ENUM(m, PatternKind);
    EXPOSE_ENUM(m, TimingControlKind);
    EXPOSE_ENUM(m, ConstraintKind);
    EXPOSE_ENUM(m, AssertionExprKind);
    EXPOSE_ENUM(m, UnaryAssertionOperator);
    EXPOSE_ENUM(m, BinaryAssertionOperator);
    EXPOSE_ENUM(m, BinsSelectExprKind);
    EXPOSE_ENUM(m, DimensionKind);

    py::enum_<VisitAction>(m, "VisitAction")
        .value("Advance", VisitAction::Advance)
        .value("Skip", VisitAction::Skip)
        .value("Interrupt", VisitAction::Interrupt);

    py::enum_<EvalFlags>(m, "EvalFlags")
        .value("None", EvalFlags::None)
        .value("IsScript", EvalFlags::IsScript)
        .value("CacheResults", EvalFlags::CacheResults)
        .value("SpecparamsAllowed", EvalFlags::SpecparamsAllowed)
        .value("CovergroupExpr", EvalFlags::CovergroupExpr)
        .value("AllowUnboundedPlaceholder", EvalFlags::AllowUnboundedPlaceholder);

    py::class_<EvalContext> evalCtx(m, "EvalContext");
    evalCtx
        .def(py::init<Compilation&, bitmask<EvalFlags>>(), "compilation"_a,
             "flags"_a = bitmask<EvalFlags>{})
        .def_readonly("flags", &EvalContext::flags)
        .def("createLocal", &EvalContext::createLocal, byrefint, "symbol"_a, "value"_a = nullptr)
        .def("findLocal", &EvalContext::findLocal, byrefint, "symbol"_a)
        .def("deleteLocal", &EvalContext::deleteLocal, "symbol"_a)
        .def("pushFrame", &EvalContext::pushFrame, "subroutine"_a, "callLocation"_a,
             "lookupLocation"_a)
        .def("pushEmptyFrame", &EvalContext::pushEmptyFrame)
        .def("popFrame", &EvalContext::popFrame)
        .def("pushLValue", &EvalContext::pushLValue, "lval"_a)
        .def("popLValue", &EvalContext::popLValue)
        .def("step", &EvalContext::step, "loc"_a)
        .def("setDisableTarget", &EvalContext::setDisableTarget)
        .def("dumpStack", &EvalContext::dumpStack)
        .def_property_readonly("topLValue", &EvalContext::getTopLValue)
        .def_property_readonly("inFunction", &EvalContext::inFunction)
        .def_property_readonly("cacheResults", &EvalContext::cacheResults)
        .def_property_readonly("topFrame", &EvalContext::topFrame)
        .def_property_readonly("disableTarget", &EvalContext::getDisableTarget)
        .def_property_readonly("disableRange", &EvalContext::getDisableRange)
        .def_property_readonly("diagnostics", &EvalContext::getDiagnostics)
        .def_property("queueTarget", &EvalContext::getQueueTarget, &EvalContext::setQueueTarget);

    py::class_<EvalContext::Frame>(evalCtx, "Frame")
        .def_readonly("temporaries", &EvalContext::Frame::temporaries)
        .def_readonly("subroutine", &EvalContext::Frame::subroutine)
        .def_readonly("callLocation", &EvalContext::Frame::callLocation)
        .def_readonly("lookupLocation", &EvalContext::Frame::lookupLocation);

    py::class_<LValue>(m, "LValue")
        .def(py::init<>())
        .def("bad", &LValue::bad)
        .def("resolve", &LValue::resolve, byrefint)
        .def("load", &LValue::load)
        .def("store", &LValue::store, "value"_a);

    py::enum_<ASTFlags>(m, "ASTFlags")
        .value("None", ASTFlags::None)
        .value("InsideConcatenation", ASTFlags::InsideConcatenation)
        .value("UnevaluatedBranch", ASTFlags::UnevaluatedBranch)
        .value("AllowDataType", ASTFlags::AllowDataType)
        .value("EnumInitializer", ASTFlags::EnumInitializer)
        .value("NoAttributes", ASTFlags::NoAttributes)
        .value("AssignmentAllowed", ASTFlags::AssignmentAllowed)
        .value("AssignmentDisallowed", ASTFlags::AssignmentDisallowed)
        .value("NonProcedural", ASTFlags::NonProcedural)
        .value("StaticInitializer", ASTFlags::StaticInitializer)
        .value("StreamingAllowed", ASTFlags::StreamingAllowed)
        .value("TopLevelStatement", ASTFlags::TopLevelStatement)
        .value("AllowUnboundedLiteral", ASTFlags::AllowUnboundedLiteral)
        .value("AllowUnboundedLiteralArithmetic", ASTFlags::AllowUnboundedLiteralArithmetic)
        .value("Function", ASTFlags::Function)
        .value("Final", ASTFlags::Final)
        .value("NonBlockingTimingControl", ASTFlags::NonBlockingTimingControl)
        .value("EventExpression", ASTFlags::EventExpression)
        .value("AllowTypeReferences", ASTFlags::AllowTypeReferences)
        .value("AssertionExpr", ASTFlags::AssertionExpr)
        .value("AllowClockingBlock", ASTFlags::AllowClockingBlock)
        .value("AssertionInstanceArgCheck", ASTFlags::AssertionInstanceArgCheck)
        .value("AssertionDelayOrRepetition", ASTFlags::AssertionDelayOrRepetition)
        .value("LValue", ASTFlags::LValue)
        .value("PropertyNegation", ASTFlags::PropertyNegation)
        .value("PropertyTimeAdvance", ASTFlags::PropertyTimeAdvance)
        .value("RecursivePropertyArg", ASTFlags::RecursivePropertyArg)
        .value("ConcurrentAssertActionBlock", ASTFlags::ConcurrentAssertActionBlock)
        .value("AllowCoverageSampleFormal", ASTFlags::AllowCoverageSampleFormal)
        .value("AllowCoverpoint", ASTFlags::AllowCoverpoint)
        .value("AllowNetType", ASTFlags::AllowNetType)
        .value("OutputArg", ASTFlags::OutputArg)
        .value("ProceduralAssign", ASTFlags::ProceduralAssign)
        .value("ProceduralForceRelease", ASTFlags::ProceduralForceRelease)
        .value("AllowInterconnect", ASTFlags::AllowInterconnect)
        .value("NotADriver", ASTFlags::NotADriver)
        .value("StreamingWithRange", ASTFlags::StreamingWithRange)
        .value("SpecifyBlock", ASTFlags::SpecifyBlock)
        .value("DPIArg", ASTFlags::DPIArg)
        .value("AssertionDefaultArg", ASTFlags::AssertionDefaultArg)
        .value("LAndRValue", ASTFlags::LAndRValue)
        .value("NoReference", ASTFlags::NoReference);

    py::class_<EvaluatedDimension>(m, "EvaluatedDimension")
        .def_readonly("kind", &EvaluatedDimension::kind)
        .def_readonly("range", &EvaluatedDimension::range)
        .def_readonly("associativeType", &EvaluatedDimension::associativeType)
        .def_readonly("queueMaxSize", &EvaluatedDimension::queueMaxSize)
        .def_property_readonly("isRange", &EvaluatedDimension::isRange);

    py::class_<ASTContext>(m, "ASTContext")
        .def(py::init<const Scope&, LookupLocation, bitmask<ASTFlags>>(), "scope"_a,
             "lookupLocation"_a, "flags"_a = ASTFlags::None)
        .def_readonly("scope", &ASTContext::scope)
        .def_readonly("lookupIndex", &ASTContext::lookupIndex)
        .def_readonly("flags", &ASTContext::flags)
        .def_property_readonly("getCompilation", &ASTContext::getCompilation)
        .def_property_readonly("getLocation", &ASTContext::getLocation)
        .def_property_readonly("inUnevaluatedBranch", &ASTContext::inUnevaluatedBranch)
        .def_property_readonly("getDriverKind", &ASTContext::getDriverKind)
        .def_property_readonly("getInstance", &ASTContext::getInstance)
        .def_property_readonly("getProceduralBlock", &ASTContext::getProceduralBlock)
        .def_property_readonly("getContainingSubroutine", &ASTContext::getContainingSubroutine)
        .def_property_readonly("inAlwaysCombLatch", &ASTContext::inAlwaysCombLatch)
        .def("addDiag",
             py::overload_cast<DiagCode, SourceLocation>(&ASTContext::addDiag, py::const_),
             byrefint, "code"_a, "location"_a)
        .def("addDiag", py::overload_cast<DiagCode, SourceRange>(&ASTContext::addDiag, py::const_),
             byrefint, "code"_a, "sourceRange"_a)
        .def("requireIntegral",
             py::overload_cast<const Expression&>(&ASTContext::requireIntegral, py::const_),
             "expr"_a)
        .def("requireIntegral",
             py::overload_cast<const ConstantValue&, SourceRange>(&ASTContext::requireIntegral,
                                                                  py::const_),
             "cv"_a, "range"_a)
        .def("requireNoUnknowns", &ASTContext::requireNoUnknowns, "value"_a, "range"_a)
        .def("requirePositive",
             py::overload_cast<const SVInt&, SourceRange>(&ASTContext::requirePositive, py::const_),
             "value"_a, "range"_a)
        .def("requirePositive",
             py::overload_cast<std::optional<int32_t>, SourceRange>(&ASTContext::requirePositive,
                                                                    py::const_),
             "value"_a, "range"_a)
        .def("requireGtZero", &ASTContext::requireGtZero, "value"_a, "range"_a)
        .def("requireBooleanConvertible", &ASTContext::requireBooleanConvertible, "expr"_a)
        .def("requireValidBitWidth",
             py::overload_cast<bitwidth_t, SourceRange>(&ASTContext::requireValidBitWidth,
                                                        py::const_),
             "width"_a, "range"_a)
        .def("requireValidBitWidth",
             py::overload_cast<const SVInt&, SourceRange>(&ASTContext::requireValidBitWidth,
                                                          py::const_),
             "value"_a, "range"_a)
        .def("eval", &ASTContext::eval, "expr"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("tryEval", &ASTContext::tryEval, "expr"_a)
        .def("evalInteger",
             py::overload_cast<const ExpressionSyntax&, bitmask<ASTFlags>>(&ASTContext::evalInteger,
                                                                           py::const_),
             "syntax"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("evalInteger",
             py::overload_cast<const Expression&, bitmask<EvalFlags>>(&ASTContext::evalInteger,
                                                                      py::const_),
             "expr"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("evalDimension", &ASTContext::evalDimension, "syntax"_a, "requireRange"_a,
             "isPacked"_a)
        .def("evalPackedDimension",
             py::overload_cast<const VariableDimensionSyntax&>(&ASTContext::evalPackedDimension,
                                                               py::const_),
             "syntax"_a)
        .def("evalPackedDimension",
             py::overload_cast<const ElementSelectSyntax&>(&ASTContext::evalPackedDimension,
                                                           py::const_),
             "syntax"_a)
        .def("evalUnpackedDimension", &ASTContext::evalUnpackedDimension, "syntax"_a)
        .def("requireSimpleExpr",
             py::overload_cast<const PropertyExprSyntax&>(&ASTContext::requireSimpleExpr,
                                                          py::const_),
             byrefint, "expr"_a)
        .def("requireSimpleExpr",
             py::overload_cast<const PropertyExprSyntax&, DiagCode>(&ASTContext::requireSimpleExpr,
                                                                    py::const_),
             byrefint, "expr"_a, "code"_a)
        .def("getRandMode", &ASTContext::getRandMode, "symbol"_a)
        .def("addAssertionBacktrace", &ASTContext::addAssertionBacktrace, "diag"_a)
        .def("resetFlags", &ASTContext::resetFlags, "addedFlags"_a);

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
        .def("eval", &Expression::eval, "context"_a)
        .def("evalLValue", &Expression::evalLValue, "context"_a)
        .def("isImplicitlyAssignableTo", &Expression::isImplicitlyAssignableTo, "compilation"_a,
             "type"_a)
        .def("getSymbolReference", &Expression::getSymbolReference, byrefint,
             "allowPacked"_a = true)
        .def("visit", &pyASTVisit<Expression>, "f"_a, PyASTVisitor::doc)
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
        .def_property_readonly("targetType", [](const TypeReferenceExpression& self) {
            return &self.targetType;
        });

    py::class_<ArbitrarySymbolExpression, Expression>(m, "ArbitrarySymbolExpression")
        .def_readonly("symbol", &ArbitrarySymbolExpression::symbol);

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

    py::class_<StreamingConcatenationExpression, Expression> streamConcatExpr(
        m, "StreamingConcatenationExpression");
    streamConcatExpr.def_readonly("sliceSize", &StreamingConcatenationExpression::sliceSize)
        .def_property_readonly("isFixedSize", &StreamingConcatenationExpression::isFixedSize)
        .def_property_readonly("bitstreamWidth", &StreamingConcatenationExpression::bitstreamWidth)
        .def_property_readonly("streams", &StreamingConcatenationExpression::streams);

    py::class_<StreamingConcatenationExpression::StreamExpression>(streamConcatExpr,
                                                                   "StreamExpression")
        .def_readonly("operand", &StreamingConcatenationExpression::StreamExpression::operand)
        .def_readonly("withExpr", &StreamingConcatenationExpression::StreamExpression::withExpr)
        .def_readonly("constantWithWidth",
                      &StreamingConcatenationExpression::StreamExpression::constantWithWidth);

    py::class_<OpenRangeExpression, Expression>(m, "OpenRangeExpression")
        .def_property_readonly("left", py::overload_cast<>(&OpenRangeExpression::left))
        .def_property_readonly("right", py::overload_cast<>(&OpenRangeExpression::right));

    py::class_<ElementSelectExpression, Expression>(m, "ElementSelectExpression")
        .def_property_readonly("value", py::overload_cast<>(&ElementSelectExpression::value))
        .def_property_readonly("selector", &ElementSelectExpression::selector);

    py::class_<RangeSelectExpression, Expression>(m, "RangeSelectExpression")
        .def_property_readonly("selectionKind", &RangeSelectExpression::getSelectionKind)
        .def_property_readonly("value", py::overload_cast<>(&RangeSelectExpression::value))
        .def_property_readonly("left", &RangeSelectExpression::left)
        .def_property_readonly("right", &RangeSelectExpression::right);

    py::class_<MemberAccessExpression, Expression>(m, "MemberAccessExpression")
        .def_property_readonly("value", py::overload_cast<>(&MemberAccessExpression::value))
        .def_property_readonly("member",
                               [](const MemberAccessExpression& self) { return &self.member; });

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
        .def_readonly("isHierarchical", &DisableStatement::isHierarchical)
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

    py::class_<Pattern>(m, "Pattern")
        .def_readonly("kind", &Pattern::kind)
        .def_readonly("syntax", &Pattern::syntax)
        .def_readonly("sourceRange", &Pattern::sourceRange)
        .def_property_readonly("bad", &Pattern::bad)
        .def("eval", &Pattern::eval, "context"_a, "value"_a, "conditionKind"_a)
        .def("__repr__", [](const Pattern& self) {
            return fmt::format("Pattern(PatternKind.{})", toString(self.kind));
        });

    py::class_<InvalidPattern, Pattern>(m, "InvalidPattern");
    py::class_<WildcardPattern, Pattern>(m, "WildcardPattern");

    py::class_<ConstantPattern, Pattern>(m, "ConstantPattern")
        .def_property_readonly("expr", [](const ConstantPattern& self) { return &self.expr; });

    py::class_<VariablePattern, Pattern>(m, "VariablePattern")
        .def_property_readonly("variable",
                               [](const VariablePattern& self) { return &self.variable; });

    py::class_<TaggedPattern, Pattern>(m, "TaggedPattern")
        .def_readonly("valuePattern", &TaggedPattern::valuePattern)
        .def_property_readonly("member", [](const TaggedPattern& self) { return &self.member; });

    py::class_<StructurePattern, Pattern> structPattern(m, "StructurePattern");
    structPattern.def_readonly("patterns", &StructurePattern::patterns);

    py::class_<StructurePattern::FieldPattern>(structPattern, "FieldPattern")
        .def_readonly("field", &StructurePattern::FieldPattern::field)
        .def_readonly("pattern", &StructurePattern::FieldPattern::pattern);

    py::class_<TimingControl>(m, "TimingControl")
        .def_readonly("kind", &TimingControl::kind)
        .def_readonly("syntax", &TimingControl::syntax)
        .def_readonly("sourceRange", &TimingControl::sourceRange)
        .def_property_readonly("bad", &TimingControl::bad)
        .def("visit", &pyASTVisit<TimingControl>, "f"_a, PyASTVisitor::doc)
        .def("__repr__", [](const TimingControl& self) {
            return fmt::format("TimingControl(TimingControlKind.{})", toString(self.kind));
        });

    py::class_<InvalidTimingControl, TimingControl>(m, "InvalidTimingControl");
    py::class_<ImplicitEventControl, TimingControl>(m, "ImplicitEventControl");
    py::class_<OneStepDelayControl, TimingControl>(m, "OneStepDelayControl");

    py::class_<DelayControl, TimingControl>(m, "DelayControl")
        .def_property_readonly("expr", [](const DelayControl& self) { return &self.expr; });

    py::class_<Delay3Control, TimingControl>(m, "Delay3Control")
        .def_property_readonly("expr1", [](const Delay3Control& self) { return &self.expr1; })
        .def_readonly("expr2", &Delay3Control::expr2)
        .def_readonly("expr3", &Delay3Control::expr3);

    py::class_<SignalEventControl, TimingControl>(m, "SignalEventControl")
        .def_property_readonly("expr", [](const SignalEventControl& self) { return &self.expr; })
        .def_readonly("iffCondition", &SignalEventControl::iffCondition)
        .def_readonly("edge", &SignalEventControl::edge);

    py::class_<EventListControl, TimingControl>(m, "EventListControl")
        .def_readonly("events", &EventListControl::events);

    py::class_<RepeatedEventControl, TimingControl>(m, "RepeatedEventControl")
        .def_property_readonly("expr", [](const RepeatedEventControl& self) { return &self.expr; })
        .def_property_readonly("event",
                               [](const RepeatedEventControl& self) { return &self.event; });

    py::class_<CycleDelayControl, TimingControl>(m, "CycleDelayControl")
        .def_property_readonly("expr", [](const CycleDelayControl& self) { return &self.expr; });

    py::class_<BlockEventListControl, TimingControl> blockEventListCtrl(m, "BlockEventListControl");
    blockEventListCtrl.def_readonly("events", &BlockEventListControl::events);

    py::class_<BlockEventListControl::Event>(blockEventListCtrl, "Event")
        .def_readonly("target", &BlockEventListControl::Event::target)
        .def_readonly("isBegin", &BlockEventListControl::Event::isBegin);

    py::class_<Constraint>(m, "Constraint")
        .def_readonly("kind", &Constraint::kind)
        .def_readonly("syntax", &Constraint::syntax)
        .def_property_readonly("bad", &Constraint::bad)
        .def("__repr__", [](const Constraint& self) {
            return fmt::format("Constraint(ConstraintKind.{})", toString(self.kind));
        });

    py::class_<InvalidConstraint, Constraint>(m, "InvalidConstraint");

    py::class_<ConstraintList, Constraint>(m, "ConstraintList")
        .def_readonly("list", &ConstraintList::list);

    py::class_<ExpressionConstraint, Constraint>(m, "ExpressionConstraint")
        .def_readonly("isSoft", &ExpressionConstraint::isSoft)
        .def_property_readonly("expr", [](const ExpressionConstraint& self) { return &self.expr; });

    py::class_<ImplicationConstraint, Constraint>(m, "ImplicationConstraint")
        .def_property_readonly("predicate",
                               [](const ImplicationConstraint& self) { return &self.predicate; })
        .def_property_readonly("body",
                               [](const ImplicationConstraint& self) { return &self.body; });

    py::class_<ConditionalConstraint, Constraint>(m, "ConditionalConstraint")
        .def_property_readonly("predicate",
                               [](const ConditionalConstraint& self) { return &self.predicate; })
        .def_property_readonly("ifBody",
                               [](const ConditionalConstraint& self) { return &self.ifBody; })
        .def_readonly("elseBody", &ConditionalConstraint::elseBody);

    py::class_<UniquenessConstraint, Constraint>(m, "UniquenessConstraint")
        .def_readonly("items", &UniquenessConstraint::items);

    py::class_<DisableSoftConstraint, Constraint>(m, "DisableSoftConstraint")
        .def_property_readonly("target",
                               [](const DisableSoftConstraint& self) { return &self.target; });

    py::class_<SolveBeforeConstraint, Constraint>(m, "SolveBeforeConstraint")
        .def_readonly("solve", &SolveBeforeConstraint::solve)
        .def_readonly("before", &SolveBeforeConstraint::before);

    py::class_<ForeachConstraint, Constraint>(m, "ForeachConstraint")
        .def_property_readonly("arrayRef",
                               [](const ForeachConstraint& self) { return &self.arrayRef; })
        .def_property_readonly("body", [](const ForeachConstraint& self) { return &self.body; })
        .def_readonly("loopDims", &ForeachConstraint::loopDims);

    py::class_<AssertionExpr>(m, "AssertionExpr")
        .def_readonly("kind", &AssertionExpr::kind)
        .def_readonly("syntax", &AssertionExpr::syntax)
        .def_property_readonly("bad", &AssertionExpr::bad)
        .def_property_readonly("admitsEmpty", &AssertionExpr::admitsEmpty)
        .def("__repr__", [](const AssertionExpr& self) {
            return fmt::format("AssertionExpr(AssertionExprKind.{})", toString(self.kind));
        });

    py::class_<InvalidAssertionExpr, AssertionExpr>(m, "InvalidAssertionExpr");

    py::class_<SequenceRange>(m, "SequenceRange")
        .def_readonly("min", &SequenceRange::min)
        .def_readonly("max", &SequenceRange::max);

    py::class_<SequenceRepetition> seqRep(m, "SequenceRepetition");
    seqRep.def_readonly("kind", &SequenceRepetition::kind)
        .def_readonly("range", &SequenceRepetition::range)
        .def_property_readonly("admitsEmpty", &SequenceRepetition::admitsEmpty);

    py::enum_<SequenceRepetition::Kind>(seqRep, "Kind")
        .value("Consecutive", SequenceRepetition::Kind::Consecutive)
        .value("Nonconsecutive", SequenceRepetition::Kind::Nonconsecutive)
        .value("GoTo", SequenceRepetition::Kind::GoTo)
        .export_values();

    py::enum_<SequenceRepetition::AdmitsEmpty>(seqRep, "AdmitsEmpty")
        .value("Yes", SequenceRepetition::AdmitsEmpty::Yes)
        .value("No", SequenceRepetition::AdmitsEmpty::No)
        .value("Depends", SequenceRepetition::AdmitsEmpty::Depends);

    py::class_<SimpleAssertionExpr, AssertionExpr>(m, "SimpleAssertionExpr")
        .def_property_readonly("expr", [](const SimpleAssertionExpr& self) { return &self.expr; })
        .def_readonly("repetition", &SimpleAssertionExpr::repetition);

    py::class_<SequenceConcatExpr, AssertionExpr> seqConcat(m, "SequenceConcatExpr");
    seqConcat.def_readonly("elements", &SequenceConcatExpr::elements);

    py::class_<SequenceConcatExpr::Element>(seqConcat, "Element")
        .def_readonly("delay", &SequenceConcatExpr::Element::delay)
        .def_readonly("sequence", &SequenceConcatExpr::Element::sequence);

    py::class_<SequenceWithMatchExpr, AssertionExpr>(m, "SequenceWithMatchExpr")
        .def_property_readonly("expr", [](const SequenceWithMatchExpr& self) { return &self.expr; })
        .def_readonly("repetition", &SequenceWithMatchExpr::repetition)
        .def_readonly("matchItems", &SequenceWithMatchExpr::matchItems);

    py::class_<UnaryAssertionExpr, AssertionExpr>(m, "UnaryAssertionExpr")
        .def_property_readonly("expr", [](const UnaryAssertionExpr& self) { return &self.expr; })
        .def_readonly("op", &UnaryAssertionExpr::op)
        .def_readonly("range", &UnaryAssertionExpr::range);

    py::class_<BinaryAssertionExpr, AssertionExpr>(m, "BinaryAssertionExpr")
        .def_property_readonly("left", [](const BinaryAssertionExpr& self) { return &self.left; })
        .def_property_readonly("right", [](const BinaryAssertionExpr& self) { return &self.right; })
        .def_readonly("op", &BinaryAssertionExpr::op);

    py::class_<FirstMatchAssertionExpr, AssertionExpr>(m, "FirstMatchAssertionExpr")
        .def_property_readonly("seq", [](const FirstMatchAssertionExpr& self) { return &self.seq; })
        .def_readonly("matchItems", &FirstMatchAssertionExpr::matchItems);

    py::class_<ClockingAssertionExpr, AssertionExpr>(m, "ClockingAssertionExpr")
        .def_property_readonly("clocking",
                               [](const ClockingAssertionExpr& self) { return &self.clocking; })
        .def_property_readonly("expr",
                               [](const ClockingAssertionExpr& self) { return &self.expr; });

    py::class_<StrongWeakAssertionExpr, AssertionExpr> strongWeakExpr(m, "StrongWeakAssertionExpr");
    strongWeakExpr
        .def_property_readonly("expr",
                               [](const StrongWeakAssertionExpr& self) { return &self.expr; })
        .def_readonly("strength", &StrongWeakAssertionExpr::strength);

    py::enum_<StrongWeakAssertionExpr::Strength>(strongWeakExpr, "Strength")
        .value("Strong", StrongWeakAssertionExpr::Strong)
        .value("Weak", StrongWeakAssertionExpr::Weak)
        .export_values();

    py::class_<AbortAssertionExpr, AssertionExpr> abortExpr(m, "AbortAssertionExpr");
    abortExpr
        .def_property_readonly("condition",
                               [](const AbortAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("expr", [](const AbortAssertionExpr& self) { return &self.expr; })
        .def_readonly("action", &AbortAssertionExpr::action)
        .def_readonly("isSync", &AbortAssertionExpr::isSync);

    py::enum_<AbortAssertionExpr::Action>(abortExpr, "Action")
        .value("Accept", AbortAssertionExpr::Accept)
        .value("Reject", AbortAssertionExpr::Reject)
        .export_values();

    py::class_<ConditionalAssertionExpr, AssertionExpr>(m, "ConditionalAssertionExpr")
        .def_property_readonly("condition",
                               [](const ConditionalAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("ifExpr",
                               [](const ConditionalAssertionExpr& self) { return &self.ifExpr; })
        .def_readonly("elseExpr", &ConditionalAssertionExpr::elseExpr);

    py::class_<CaseAssertionExpr, AssertionExpr> caseAssertExpr(m, "CaseAssertionExpr");
    caseAssertExpr
        .def_property_readonly("expr", [](const CaseAssertionExpr& self) { return &self.expr; })
        .def_readonly("items", &CaseAssertionExpr::items)
        .def_readonly("defaultCase", &CaseAssertionExpr::defaultCase);

    py::class_<CaseAssertionExpr::ItemGroup>(caseAssertExpr, "ItemGroup")
        .def_readonly("expressions", &CaseAssertionExpr::ItemGroup::expressions)
        .def_readonly("body", &CaseAssertionExpr::ItemGroup::body);

    py::class_<DisableIffAssertionExpr, AssertionExpr>(m, "DisableIffAssertionExpr")
        .def_property_readonly("condition",
                               [](const DisableIffAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("expr",
                               [](const DisableIffAssertionExpr& self) { return &self.expr; });

    py::class_<BinsSelectExpr>(m, "BinsSelectExpr")
        .def_readonly("kind", &BinsSelectExpr::kind)
        .def_readonly("syntax", &BinsSelectExpr::syntax)
        .def_property_readonly("bad", &BinsSelectExpr::bad)
        .def("__repr__", [](const BinsSelectExpr& self) {
            return fmt::format("BinsSelectExpr(BinsSelectExprKind.{})", toString(self.kind));
        });

    py::class_<InvalidBinsSelectExpr, BinsSelectExpr>(m, "InvalidBinsSelectExpr");
    py::class_<CrossIdBinsSelectExpr, BinsSelectExpr>(m, "CrossIdBinsSelectExpr");

    py::class_<ConditionBinsSelectExpr, BinsSelectExpr>(m, "ConditionBinsSelectExpr")
        .def_property_readonly("target",
                               [](const ConditionBinsSelectExpr& self) { return &self.target; })
        .def_readonly("intersects", &ConditionBinsSelectExpr::intersects);

    py::class_<UnaryBinsSelectExpr, BinsSelectExpr> ubse(m, "UnaryBinsSelectExpr");
    ubse.def_property_readonly("expr", [](const UnaryBinsSelectExpr& self) { return &self.expr; })
        .def_readonly("op", &UnaryBinsSelectExpr::op);

    py::enum_<UnaryBinsSelectExpr::Op>(ubse, "Op")
        .value("Negation", UnaryBinsSelectExpr::Negation)
        .export_values();

    py::class_<BinaryBinsSelectExpr, BinsSelectExpr> bbse(m, "BinaryBinsSelectExpr");
    bbse.def_property_readonly("left", [](const BinaryBinsSelectExpr& self) { return &self.left; })
        .def_property_readonly("right",
                               [](const BinaryBinsSelectExpr& self) { return &self.right; })
        .def_readonly("op", &BinaryBinsSelectExpr::op);

    py::enum_<BinaryBinsSelectExpr::Op>(bbse, "Op")
        .value("And", BinaryBinsSelectExpr::And)
        .value("Or", BinaryBinsSelectExpr::Or)
        .export_values();

    py::class_<SetExprBinsSelectExpr, BinsSelectExpr>(m, "SetExprBinsSelectExpr")
        .def_property_readonly("expr", [](const SetExprBinsSelectExpr& self) { return &self.expr; })
        .def_readonly("matchesExpr", &SetExprBinsSelectExpr::matchesExpr);

    py::class_<BinSelectWithFilterExpr, BinsSelectExpr>(m, "BinSelectWithFilterExpr")
        .def_property_readonly("expr",
                               [](const BinSelectWithFilterExpr& self) { return &self.expr; })
        .def_property_readonly("filter",
                               [](const BinSelectWithFilterExpr& self) { return &self.filter; })
        .def_readonly("matchesExpr", &BinSelectWithFilterExpr::matchesExpr);
}
