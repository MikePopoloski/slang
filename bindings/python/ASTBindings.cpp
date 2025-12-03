//------------------------------------------------------------------------------
// ASTBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/syntax/AllSyntax.h"

void registerAST(py::module_& m) {
    EXPOSE_ENUM(m, PatternKind);
    EXPOSE_ENUM(m, TimingControlKind);
    EXPOSE_ENUM(m, ConstraintKind);
    EXPOSE_ENUM(m, AssertionExprKind);
    EXPOSE_ENUM(m, UnaryAssertionOperator);
    EXPOSE_ENUM(m, BinaryAssertionOperator);
    EXPOSE_ENUM(m, BinsSelectExprKind);
    EXPOSE_ENUM(m, DimensionKind);
    EXPOSE_ENUM(m, ValueRangeKind);

    py::native_enum<VisitAction>(m, "VisitAction", "enum.Enum")
        .value("Advance", VisitAction::Advance)
        .value("Skip", VisitAction::Skip)
        .value("Interrupt", VisitAction::Interrupt)
        .finalize();

    py::native_enum<EvalFlags>(m, "EvalFlags", "enum.Flag")
        .value("None_", EvalFlags::None)
        .value("IsScript", EvalFlags::IsScript)
        .value("CacheResults", EvalFlags::CacheResults)
        .value("SpecparamsAllowed", EvalFlags::SpecparamsAllowed)
        .value("AllowUnboundedPlaceholder", EvalFlags::AllowUnboundedPlaceholder)
        .finalize();

    py::classh<EvalContext> evalCtx(m, "EvalContext");
    evalCtx
        .def(py::init<const ASTContext&, bitmask<EvalFlags>>(), "astCtx"_a,
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
        .def_property_readonly("diagnostics", &EvalContext::getAllDiagnostics)
        .def_property("queueTarget", &EvalContext::getQueueTarget, &EvalContext::setQueueTarget);

    py::classh<EvalContext::Frame>(evalCtx, "Frame")
        .def_readonly("temporaries", &EvalContext::Frame::temporaries)
        .def_readonly("subroutine", &EvalContext::Frame::subroutine)
        .def_readonly("callLocation", &EvalContext::Frame::callLocation)
        .def_readonly("lookupLocation", &EvalContext::Frame::lookupLocation);

    py::classh<LValue>(m, "LValue")
        .def(py::init<>())
        .def("bad", &LValue::bad)
        .def("resolve", &LValue::resolve, byrefint)
        .def("load", &LValue::load)
        .def("store", &LValue::store, "value"_a);

    py::native_enum<ASTFlags>(m, "ASTFlags", "enum.Flag")
        .value("None_", ASTFlags::None)
        .value("InsideConcatenation", ASTFlags::InsideConcatenation)
        .value("UnevaluatedBranch", ASTFlags::UnevaluatedBranch)
        .value("AllowDataType", ASTFlags::AllowDataType)
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
        .value("AllowInterconnect", ASTFlags::AllowInterconnect)
        .value("StreamingWithRange", ASTFlags::StreamingWithRange)
        .value("SpecifyBlock", ASTFlags::SpecifyBlock)
        .value("SpecparamInitializer", ASTFlags::SpecparamInitializer)
        .value("DPIArg", ASTFlags::DPIArg)
        .value("AssertionDefaultArg", ASTFlags::AssertionDefaultArg)
        .value("LAndRValue", ASTFlags::LAndRValue)
        .value("NoReference", ASTFlags::NoReference)
        .value("ConfigParam", ASTFlags::ConfigParam)
        .value("TypeOperator", ASTFlags::TypeOperator)
        .value("ForkJoinAnyNone", ASTFlags::ForkJoinAnyNone)
        .value("DisallowUDNT", ASTFlags::DisallowUDNT)
        .value("BindInstantiation", ASTFlags::BindInstantiation)
        .value("WildcardPortConn", ASTFlags::WildcardPortConn)
        .finalize();

    py::classh<EvaluatedDimension>(m, "EvaluatedDimension")
        .def_readonly("kind", &EvaluatedDimension::kind)
        .def_readonly("range", &EvaluatedDimension::range)
        .def_readonly("associativeType", &EvaluatedDimension::associativeType)
        .def_readonly("queueMaxSize", &EvaluatedDimension::queueMaxSize)
        .def_property_readonly("isRange", &EvaluatedDimension::isRange);

    py::classh<ASTContext>(m, "ASTContext")
        .def(py::init<const Scope&, LookupLocation, bitmask<ASTFlags>>(), "scope"_a,
             "lookupLocation"_a, "flags"_a = ASTFlags::None)
        .def_readonly("scope", &ASTContext::scope)
        .def_readonly("lookupIndex", &ASTContext::lookupIndex)
        .def_readonly("flags", &ASTContext::flags)
        .def_property_readonly("getCompilation", &ASTContext::getCompilation)
        .def_property_readonly("getLocation", &ASTContext::getLocation)
        .def_property_readonly("inUnevaluatedBranch", &ASTContext::inUnevaluatedBranch)
        .def_property_readonly("getInstance", &ASTContext::getInstance)
        .def_property_readonly("getProceduralBlock", &ASTContext::getProceduralBlock)
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

    py::classh<Pattern>(m, "Pattern")
        .def_readonly("kind", &Pattern::kind)
        .def_readonly("syntax", &Pattern::syntax)
        .def_readonly("sourceRange", &Pattern::sourceRange)
        .def_property_readonly("bad", &Pattern::bad)
        .def("eval", &Pattern::eval, "context"_a, "value"_a, "conditionKind"_a)
        .def("isEquivalentTo", &Pattern::isEquivalentTo, "other"_a)
        .def("__repr__", [](const Pattern& self) {
            return fmt::format("Pattern(PatternKind.{})", toString(self.kind));
        });

    py::classh<InvalidPattern, Pattern>(m, "InvalidPattern");
    py::classh<WildcardPattern, Pattern>(m, "WildcardPattern");

    py::classh<ConstantPattern, Pattern>(m, "ConstantPattern")
        .def_property_readonly("expr", [](const ConstantPattern& self) { return &self.expr; });

    py::classh<VariablePattern, Pattern>(m, "VariablePattern")
        .def_property_readonly("variable",
                               [](const VariablePattern& self) { return &self.variable; });

    py::classh<TaggedPattern, Pattern>(m, "TaggedPattern")
        .def_readonly("valuePattern", &TaggedPattern::valuePattern)
        .def_property_readonly("member", [](const TaggedPattern& self) { return &self.member; });

    py::classh<StructurePattern, Pattern> structPattern(m, "StructurePattern");
    structPattern.def_readonly("patterns", &StructurePattern::patterns);

    py::classh<StructurePattern::FieldPattern>(structPattern, "FieldPattern")
        .def_readonly("field", &StructurePattern::FieldPattern::field)
        .def_readonly("pattern", &StructurePattern::FieldPattern::pattern);

    py::classh<TimingControl>(m, "TimingControl")
        .def_readonly("kind", &TimingControl::kind)
        .def_readonly("syntax", &TimingControl::syntax)
        .def_readonly("sourceRange", &TimingControl::sourceRange)
        .def_property_readonly("bad", &TimingControl::bad)
        .def("isEquivalentTo", &TimingControl::isEquivalentTo, "other"_a)
        .def("visit", &pyASTVisit<TimingControl>, "f"_a, PyASTVisitor::doc)
        .def("__repr__", [](const TimingControl& self) {
            return fmt::format("TimingControl(TimingControlKind.{})", toString(self.kind));
        });

    py::classh<InvalidTimingControl, TimingControl>(m, "InvalidTimingControl");
    py::classh<ImplicitEventControl, TimingControl>(m, "ImplicitEventControl");
    py::classh<OneStepDelayControl, TimingControl>(m, "OneStepDelayControl");

    py::classh<DelayControl, TimingControl>(m, "DelayControl")
        .def_property_readonly("expr", [](const DelayControl& self) { return &self.expr; });

    py::classh<Delay3Control, TimingControl>(m, "Delay3Control")
        .def_property_readonly("expr1", [](const Delay3Control& self) { return &self.expr1; })
        .def_readonly("expr2", &Delay3Control::expr2)
        .def_readonly("expr3", &Delay3Control::expr3);

    py::classh<SignalEventControl, TimingControl>(m, "SignalEventControl")
        .def_property_readonly("expr", [](const SignalEventControl& self) { return &self.expr; })
        .def_readonly("iffCondition", &SignalEventControl::iffCondition)
        .def_readonly("edge", &SignalEventControl::edge);

    py::classh<EventListControl, TimingControl>(m, "EventListControl")
        .def_readonly("events", &EventListControl::events);

    py::classh<RepeatedEventControl, TimingControl>(m, "RepeatedEventControl")
        .def_property_readonly("expr", [](const RepeatedEventControl& self) { return &self.expr; })
        .def_property_readonly("event",
                               [](const RepeatedEventControl& self) { return &self.event; });

    py::classh<CycleDelayControl, TimingControl>(m, "CycleDelayControl")
        .def_property_readonly("expr", [](const CycleDelayControl& self) { return &self.expr; });

    py::classh<BlockEventListControl, TimingControl> blockEventListCtrl(m, "BlockEventListControl");
    blockEventListCtrl.def_readonly("events", &BlockEventListControl::events);

    py::classh<BlockEventListControl::Event>(blockEventListCtrl, "Event")
        .def_readonly("target", &BlockEventListControl::Event::target)
        .def_readonly("isBegin", &BlockEventListControl::Event::isBegin);

    py::classh<Constraint>(m, "Constraint")
        .def_readonly("kind", &Constraint::kind)
        .def_readonly("syntax", &Constraint::syntax)
        .def_property_readonly("bad", &Constraint::bad)
        .def("isEquivalentTo", &Constraint::isEquivalentTo, "other"_a)
        .def("__repr__", [](const Constraint& self) {
            return fmt::format("Constraint(ConstraintKind.{})", toString(self.kind));
        });

    py::classh<InvalidConstraint, Constraint>(m, "InvalidConstraint");

    py::classh<ConstraintList, Constraint>(m, "ConstraintList")
        .def_readonly("list", &ConstraintList::list);

    py::classh<ExpressionConstraint, Constraint>(m, "ExpressionConstraint")
        .def_readonly("isSoft", &ExpressionConstraint::isSoft)
        .def_property_readonly("expr", [](const ExpressionConstraint& self) { return &self.expr; });

    py::classh<ImplicationConstraint, Constraint>(m, "ImplicationConstraint")
        .def_property_readonly("predicate",
                               [](const ImplicationConstraint& self) { return &self.predicate; })
        .def_property_readonly("body",
                               [](const ImplicationConstraint& self) { return &self.body; });

    py::classh<ConditionalConstraint, Constraint>(m, "ConditionalConstraint")
        .def_property_readonly("predicate",
                               [](const ConditionalConstraint& self) { return &self.predicate; })
        .def_property_readonly("ifBody",
                               [](const ConditionalConstraint& self) { return &self.ifBody; })
        .def_readonly("elseBody", &ConditionalConstraint::elseBody);

    py::classh<UniquenessConstraint, Constraint>(m, "UniquenessConstraint")
        .def_readonly("items", &UniquenessConstraint::items);

    py::classh<DisableSoftConstraint, Constraint>(m, "DisableSoftConstraint")
        .def_property_readonly("target",
                               [](const DisableSoftConstraint& self) { return &self.target; });

    py::classh<SolveBeforeConstraint, Constraint>(m, "SolveBeforeConstraint")
        .def_readonly("solve", &SolveBeforeConstraint::solve)
        .def_readonly("after", &SolveBeforeConstraint::after);

    py::classh<ForeachConstraint, Constraint>(m, "ForeachConstraint")
        .def_property_readonly("arrayRef",
                               [](const ForeachConstraint& self) { return &self.arrayRef; })
        .def_property_readonly("body", [](const ForeachConstraint& self) { return &self.body; })
        .def_readonly("loopDims", &ForeachConstraint::loopDims);

    py::classh<AssertionExpr>(m, "AssertionExpr")
        .def_readonly("kind", &AssertionExpr::kind)
        .def_readonly("syntax", &AssertionExpr::syntax)
        .def_property_readonly("bad", &AssertionExpr::bad)
        .def("isEquivalentTo", &AssertionExpr::isEquivalentTo, "other"_a)
        .def("__repr__", [](const AssertionExpr& self) {
            return fmt::format("AssertionExpr(AssertionExprKind.{})", toString(self.kind));
        });

    py::classh<InvalidAssertionExpr, AssertionExpr>(m, "InvalidAssertionExpr");

    py::classh<SequenceRange>(m, "SequenceRange")
        .def_readonly("min", &SequenceRange::min)
        .def_readonly("max", &SequenceRange::max);

    py::classh<SequenceRepetition> seqRep(m, "SequenceRepetition");
    seqRep.def_readonly("kind", &SequenceRepetition::kind)
        .def_readonly("range", &SequenceRepetition::range);

    py::native_enum<SequenceRepetition::Kind>(seqRep, "Kind", "enum.Enum")
        .value("Consecutive", SequenceRepetition::Kind::Consecutive)
        .value("Nonconsecutive", SequenceRepetition::Kind::Nonconsecutive)
        .value("GoTo", SequenceRepetition::Kind::GoTo)
        .export_values()
        .finalize();

    py::classh<SimpleAssertionExpr, AssertionExpr>(m, "SimpleAssertionExpr")
        .def_property_readonly("expr", [](const SimpleAssertionExpr& self) { return &self.expr; })
        .def_readonly("repetition", &SimpleAssertionExpr::repetition);

    py::classh<SequenceConcatExpr, AssertionExpr> seqConcat(m, "SequenceConcatExpr");
    seqConcat.def_readonly("elements", &SequenceConcatExpr::elements);

    py::classh<SequenceConcatExpr::Element>(seqConcat, "Element")
        .def_readonly("delay", &SequenceConcatExpr::Element::delay)
        .def_readonly("sequence", &SequenceConcatExpr::Element::sequence);

    py::classh<SequenceWithMatchExpr, AssertionExpr>(m, "SequenceWithMatchExpr")
        .def_property_readonly("expr", [](const SequenceWithMatchExpr& self) { return &self.expr; })
        .def_readonly("repetition", &SequenceWithMatchExpr::repetition)
        .def_readonly("matchItems", &SequenceWithMatchExpr::matchItems);

    py::classh<UnaryAssertionExpr, AssertionExpr>(m, "UnaryAssertionExpr")
        .def_property_readonly("expr", [](const UnaryAssertionExpr& self) { return &self.expr; })
        .def_readonly("op", &UnaryAssertionExpr::op)
        .def_readonly("range", &UnaryAssertionExpr::range);

    py::classh<BinaryAssertionExpr, AssertionExpr>(m, "BinaryAssertionExpr")
        .def_property_readonly("left", [](const BinaryAssertionExpr& self) { return &self.left; })
        .def_property_readonly("right", [](const BinaryAssertionExpr& self) { return &self.right; })
        .def_readonly("op", &BinaryAssertionExpr::op);

    py::classh<FirstMatchAssertionExpr, AssertionExpr>(m, "FirstMatchAssertionExpr")
        .def_property_readonly("seq", [](const FirstMatchAssertionExpr& self) { return &self.seq; })
        .def_readonly("matchItems", &FirstMatchAssertionExpr::matchItems);

    py::classh<ClockingAssertionExpr, AssertionExpr>(m, "ClockingAssertionExpr")
        .def_property_readonly("clocking",
                               [](const ClockingAssertionExpr& self) { return &self.clocking; })
        .def_property_readonly("expr",
                               [](const ClockingAssertionExpr& self) { return &self.expr; });

    py::classh<StrongWeakAssertionExpr, AssertionExpr> strongWeakExpr(m, "StrongWeakAssertionExpr");
    strongWeakExpr
        .def_property_readonly("expr",
                               [](const StrongWeakAssertionExpr& self) { return &self.expr; })
        .def_readonly("strength", &StrongWeakAssertionExpr::strength);

    py::native_enum<StrongWeakAssertionExpr::Strength>(strongWeakExpr, "Strength", "enum.Enum")
        .value("Strong", StrongWeakAssertionExpr::Strong)
        .value("Weak", StrongWeakAssertionExpr::Weak)
        .export_values()
        .finalize();

    py::classh<AbortAssertionExpr, AssertionExpr> abortExpr(m, "AbortAssertionExpr");
    abortExpr
        .def_property_readonly("condition",
                               [](const AbortAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("expr", [](const AbortAssertionExpr& self) { return &self.expr; })
        .def_readonly("action", &AbortAssertionExpr::action)
        .def_readonly("isSync", &AbortAssertionExpr::isSync);

    py::native_enum<AbortAssertionExpr::Action>(abortExpr, "Action", "enum.Enum")
        .value("Accept", AbortAssertionExpr::Accept)
        .value("Reject", AbortAssertionExpr::Reject)
        .export_values()
        .finalize();

    py::classh<ConditionalAssertionExpr, AssertionExpr>(m, "ConditionalAssertionExpr")
        .def_property_readonly("condition",
                               [](const ConditionalAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("ifExpr",
                               [](const ConditionalAssertionExpr& self) { return &self.ifExpr; })
        .def_readonly("elseExpr", &ConditionalAssertionExpr::elseExpr);

    py::classh<CaseAssertionExpr, AssertionExpr> caseAssertExpr(m, "CaseAssertionExpr");
    caseAssertExpr
        .def_property_readonly("expr", [](const CaseAssertionExpr& self) { return &self.expr; })
        .def_readonly("items", &CaseAssertionExpr::items)
        .def_readonly("defaultCase", &CaseAssertionExpr::defaultCase);

    py::classh<CaseAssertionExpr::ItemGroup>(caseAssertExpr, "ItemGroup")
        .def_readonly("expressions", &CaseAssertionExpr::ItemGroup::expressions)
        .def_readonly("body", &CaseAssertionExpr::ItemGroup::body);

    py::classh<DisableIffAssertionExpr, AssertionExpr>(m, "DisableIffAssertionExpr")
        .def_property_readonly("condition",
                               [](const DisableIffAssertionExpr& self) { return &self.condition; })
        .def_property_readonly("expr",
                               [](const DisableIffAssertionExpr& self) { return &self.expr; });

    py::classh<BinsSelectExpr>(m, "BinsSelectExpr")
        .def_readonly("kind", &BinsSelectExpr::kind)
        .def_readonly("syntax", &BinsSelectExpr::syntax)
        .def_property_readonly("bad", &BinsSelectExpr::bad)
        .def("__repr__", [](const BinsSelectExpr& self) {
            return fmt::format("BinsSelectExpr(BinsSelectExprKind.{})", toString(self.kind));
        });

    py::classh<InvalidBinsSelectExpr, BinsSelectExpr>(m, "InvalidBinsSelectExpr");
    py::classh<CrossIdBinsSelectExpr, BinsSelectExpr>(m, "CrossIdBinsSelectExpr");

    py::classh<ConditionBinsSelectExpr, BinsSelectExpr>(m, "ConditionBinsSelectExpr")
        .def_property_readonly("target",
                               [](const ConditionBinsSelectExpr& self) { return &self.target; })
        .def_readonly("intersects", &ConditionBinsSelectExpr::intersects);

    py::classh<UnaryBinsSelectExpr, BinsSelectExpr> ubse(m, "UnaryBinsSelectExpr");
    ubse.def_property_readonly("expr", [](const UnaryBinsSelectExpr& self) { return &self.expr; })
        .def_readonly("op", &UnaryBinsSelectExpr::op);

    py::native_enum<UnaryBinsSelectExpr::Op>(ubse, "Op", "enum.Enum")
        .value("Negation", UnaryBinsSelectExpr::Negation)
        .export_values()
        .finalize();

    py::classh<BinaryBinsSelectExpr, BinsSelectExpr> bbse(m, "BinaryBinsSelectExpr");
    bbse.def_property_readonly("left", [](const BinaryBinsSelectExpr& self) { return &self.left; })
        .def_property_readonly("right",
                               [](const BinaryBinsSelectExpr& self) { return &self.right; })
        .def_readonly("op", &BinaryBinsSelectExpr::op);

    py::native_enum<BinaryBinsSelectExpr::Op>(bbse, "Op", "enum.Enum")
        .value("And", BinaryBinsSelectExpr::And)
        .value("Or", BinaryBinsSelectExpr::Or)
        .export_values()
        .finalize();

    py::classh<SetExprBinsSelectExpr, BinsSelectExpr>(m, "SetExprBinsSelectExpr")
        .def_property_readonly("expr", [](const SetExprBinsSelectExpr& self) { return &self.expr; })
        .def_readonly("matchesExpr", &SetExprBinsSelectExpr::matchesExpr);

    py::classh<BinSelectWithFilterExpr, BinsSelectExpr>(m, "BinSelectWithFilterExpr")
        .def_property_readonly("expr",
                               [](const BinSelectWithFilterExpr& self) { return &self.expr; })
        .def_property_readonly("filter",
                               [](const BinSelectWithFilterExpr& self) { return &self.filter; })
        .def_readonly("matchesExpr", &BinSelectWithFilterExpr::matchesExpr);
}
