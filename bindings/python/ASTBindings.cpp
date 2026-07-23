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
#include "slang/ast/ValuePath.h"
#include "slang/syntax/AllSyntax.h"

void registerAST(nb::module_& m) {
    EXPOSE_ENUM(m, PatternKind);
    EXPOSE_ENUM(m, TimingControlKind);
    EXPOSE_ENUM(m, ConstraintKind);
    EXPOSE_ENUM(m, AssertionExprKind);
    EXPOSE_ENUM(m, UnaryAssertionOperator);
    EXPOSE_ENUM(m, BinaryAssertionOperator);
    EXPOSE_ENUM(m, BinsSelectExprKind);
    EXPOSE_ENUM(m, DimensionKind);
    EXPOSE_ENUM(m, ValueRangeKind);

    nb::enum_<VisitAction>(m, "VisitAction")
        .value("Advance", VisitAction::Advance)
        .value("Skip", VisitAction::Skip)
        .value("Interrupt", VisitAction::Interrupt);

    nb::enum_<EvalFlags>(m, "EvalFlags", nb::is_arithmetic())
        .value("None_", EvalFlags::None)
        .value("IsScript", EvalFlags::IsScript)
        .value("CacheResults", EvalFlags::CacheResults)
        .value("SpecparamsAllowed", EvalFlags::SpecparamsAllowed)
        .value("AllowUnboundedPlaceholder", EvalFlags::AllowUnboundedPlaceholder);

    nb::class_<EvalContext> evalCtx(m, "EvalContext");
    evalCtx
        .def(nb::init<const ASTContext&, bitmask<EvalFlags>>(), "astCtx"_a,
             "flags"_a = bitmask<EvalFlags>{})
        .def(
            "__init__",
            [](EvalContext* self, const Symbol& symbol, bitmask<EvalFlags> flags) {
                if (!symbol.getParentScope()) {
                    throw std::invalid_argument(
                        "Symbol must have a parent scope to be used for EvalContext "
                        "construction");
                }
                new (self) EvalContext(symbol, flags);
            },
            "symbol"_a, "flags"_a = bitmask<EvalFlags>{})
        .def_ro("flags", &EvalContext::flags)
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
        .def_prop_ro("topLValue", &EvalContext::getTopLValue)
        .def_prop_ro("inFunction", &EvalContext::inFunction)
        .def_prop_ro("cacheResults", &EvalContext::cacheResults)
        .def_prop_ro("topFrame", &EvalContext::topFrame)
        .def_prop_ro("disableTarget", &EvalContext::getDisableTarget)
        .def_prop_ro("disableRange", &EvalContext::getDisableRange)
        .def_prop_ro("diagnostics", &EvalContext::getAllDiagnostics)
        .def_prop_rw("queueTarget", &EvalContext::getQueueTarget, &EvalContext::setQueueTarget);

    nb::class_<EvalContext::Frame>(evalCtx, "Frame")
        .def_ro("temporaries", &EvalContext::Frame::temporaries)
        .def_ro("subroutine", &EvalContext::Frame::subroutine)
        .def_ro("callLocation", &EvalContext::Frame::callLocation)
        .def_ro("lookupLocation", &EvalContext::Frame::lookupLocation);

    nb::class_<LValue>(m, "LValue")
        .def(nb::init<>())
        .def("bad", &LValue::bad)
        .def("resolve", &LValue::resolve, byrefint)
        .def("load", &LValue::load)
        .def("store", &LValue::store, "value"_a);

    nb::enum_<ASTFlags>(m, "ASTFlags", nb::is_arithmetic())
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
        .value("WildcardPortConn", ASTFlags::WildcardPortConn);

    nb::class_<EvaluatedDimension>(m, "EvaluatedDimension")
        .def_ro("kind", &EvaluatedDimension::kind)
        .def_ro("range", &EvaluatedDimension::range)
        .def_ro("associativeType", &EvaluatedDimension::associativeType)
        .def_ro("queueMaxSize", &EvaluatedDimension::queueMaxSize)
        .def_ro("leftExpr", &EvaluatedDimension::leftExpr)
        .def_ro("rightExpr", &EvaluatedDimension::rightExpr)
        .def_prop_ro("isRange", &EvaluatedDimension::isRange);

    nb::class_<ASTContext>(m, "ASTContext")
        .def(nb::init<const Scope&, LookupLocation, bitmask<ASTFlags>>(), "scope"_a,
             "lookupLocation"_a, "flags"_a = ASTFlags::None)
        .def_ro("scope", &ASTContext::scope)
        .def_ro("lookupIndex", &ASTContext::lookupIndex)
        .def_ro("flags", &ASTContext::flags)
        .def_prop_ro("getCompilation", &ASTContext::getCompilation)
        .def_prop_ro("getLocation", &ASTContext::getLocation)
        .def_prop_ro("inUnevaluatedBranch", &ASTContext::inUnevaluatedBranch)
        .def_prop_ro("getInstance", &ASTContext::getInstance)
        .def_prop_ro("getProceduralBlock", &ASTContext::getProceduralBlock)
        .def_prop_ro("inAlwaysCombLatch", &ASTContext::inAlwaysCombLatch)
        .def("addDiag",
             nb::overload_cast<DiagCode, SourceLocation>(&ASTContext::addDiag, nb::const_),
             byrefint, "code"_a, "location"_a)
        .def("addDiag", nb::overload_cast<DiagCode, SourceRange>(&ASTContext::addDiag, nb::const_),
             byrefint, "code"_a, "sourceRange"_a)
        .def("requireIntegral",
             nb::overload_cast<const Expression&>(&ASTContext::requireIntegral, nb::const_),
             "expr"_a)
        .def("requireIntegral",
             nb::overload_cast<const ConstantValue&, SourceRange>(&ASTContext::requireIntegral,
                                                                  nb::const_),
             "cv"_a, "range"_a)
        .def("requireNoUnknowns", &ASTContext::requireNoUnknowns, "value"_a, "range"_a)
        .def("requirePositive",
             nb::overload_cast<const SVInt&, SourceRange>(&ASTContext::requirePositive, nb::const_),
             "value"_a, "range"_a)
        .def("requirePositive",
             nb::overload_cast<std::optional<int32_t>, SourceRange>(&ASTContext::requirePositive,
                                                                    nb::const_),
             "value"_a, "range"_a)
        .def("requireGtZero", &ASTContext::requireGtZero, "value"_a, "range"_a)
        .def("requireBooleanConvertible", &ASTContext::requireBooleanConvertible, "expr"_a)
        .def("requireValidBitWidth",
             nb::overload_cast<bitwidth_t, SourceRange>(&ASTContext::requireValidBitWidth,
                                                        nb::const_),
             "width"_a, "range"_a)
        .def("requireValidBitWidth",
             nb::overload_cast<const SVInt&, SourceRange>(&ASTContext::requireValidBitWidth,
                                                          nb::const_),
             "value"_a, "range"_a)
        .def("eval", &ASTContext::eval, "expr"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("tryEval", &ASTContext::tryEval, "expr"_a)
        .def("evalInteger",
             nb::overload_cast<const ExpressionSyntax&, bitmask<ASTFlags>>(&ASTContext::evalInteger,
                                                                           nb::const_),
             "syntax"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("evalInteger",
             nb::overload_cast<const Expression&, bitmask<EvalFlags>>(&ASTContext::evalInteger,
                                                                      nb::const_),
             "expr"_a, "extraFlags"_a = bitmask<ASTFlags>{})
        .def("evalDimension", &ASTContext::evalDimension, "syntax"_a, "requireRange"_a,
             "isPacked"_a)
        .def("evalPackedDimension",
             nb::overload_cast<const VariableDimensionSyntax&>(&ASTContext::evalPackedDimension,
                                                               nb::const_),
             "syntax"_a)
        .def("evalPackedDimension",
             nb::overload_cast<const ElementSelectSyntax&>(&ASTContext::evalPackedDimension,
                                                           nb::const_),
             "syntax"_a)
        .def("evalUnpackedDimension", &ASTContext::evalUnpackedDimension, "syntax"_a)
        .def("requireSimpleExpr",
             nb::overload_cast<const PropertyExprSyntax&>(&ASTContext::requireSimpleExpr,
                                                          nb::const_),
             byrefint, "expr"_a)
        .def("requireSimpleExpr",
             nb::overload_cast<const PropertyExprSyntax&, DiagCode>(&ASTContext::requireSimpleExpr,
                                                                    nb::const_),
             byrefint, "expr"_a, "code"_a)
        .def("getRandMode", &ASTContext::getRandMode, "symbol"_a)
        .def("addAssertionBacktrace", &ASTContext::addAssertionBacktrace, "diag"_a)
        .def("resetFlags", &ASTContext::resetFlags, "addedFlags"_a);

    nb::class_<ValuePath>(m, "ValuePath")
        .def(nb::init<>())
        .def(nb::init<const Expression&, EvalContext&>(), "expr"_a, "evalContext"_a)
        .def_ro("rootExpr", &ValuePath::rootExpr)
        .def_ro("fullExpr", &ValuePath::fullExpr)
        .def_ro("lsp", &ValuePath::lsp)
        .def_ro("lspBounds", &ValuePath::lspBounds)
        .def_prop_ro("rootSymbol", &ValuePath::rootSymbol)
        .def_prop_ro("empty", &ValuePath::empty)
        .def_prop_ro("isFullyStatic", &ValuePath::isFullyStatic)
        .def("toString", &ValuePath::toString, "evalContext"_a)
        .def("overlaps", &ValuePath::overlaps, "other"_a)
        .def(
            "__iter__",
            [](const ValuePath& self) {
                return nb::make_iterator(nb::type<ValuePath>(), "ValuePathIterator", self.begin(),
                                         self.end());
            },
            nb::keep_alive<0, 1>())
        .def(
            "expandIndirectRefs",
            [](const ValuePath& self, BumpAllocator& alloc, EvalContext& evalContext,
               nb::callable callback) {
                self.expandIndirectRefs(alloc, evalContext,
                                        [&callback](const ValuePath& path) { callback(path); });
            },
            "alloc"_a, "evalContext"_a, "callback"_a)
        .def_static(
            "visitPaths",
            [](const Expression& expr, EvalContext& evalContext, nb::callable callback,
               bool skipSelectors) {
                ValuePath::visitPaths(
                    expr, evalContext, [&callback](const ValuePath& path) { callback(path); },
                    skipSelectors);
            },
            "expr"_a, "evalContext"_a, "callback"_a, "skipSelectors"_a = false);

    nb::class_<Pattern>(m, "Pattern")
        .def_ro("kind", &Pattern::kind)
        .def_ro("syntax", &Pattern::syntax)
        .def_ro("sourceRange", &Pattern::sourceRange)
        .def_prop_ro("bad", &Pattern::bad)
        .def("eval", &Pattern::eval, "context"_a, "value"_a, "conditionKind"_a)
        .def("isEquivalentTo", &Pattern::isEquivalentTo, "other"_a)
        .def("__repr__", [](const Pattern& self) {
            return fmt::format("Pattern(PatternKind.{})", toString(self.kind));
        });

    nb::class_<InvalidPattern, Pattern>(m, "InvalidPattern");
    nb::class_<WildcardPattern, Pattern>(m, "WildcardPattern");

    nb::class_<ConstantPattern, Pattern>(m, "ConstantPattern")
        .def_prop_ro("expr", [](const ConstantPattern& self) { return &self.expr; });

    nb::class_<VariablePattern, Pattern>(m, "VariablePattern")
        .def_prop_ro("variable", [](const VariablePattern& self) { return &self.variable; });

    nb::class_<TaggedPattern, Pattern>(m, "TaggedPattern")
        .def_ro("valuePattern", &TaggedPattern::valuePattern)
        .def_prop_ro("member", [](const TaggedPattern& self) { return &self.member; });

    nb::class_<StructurePattern, Pattern> structPattern(m, "StructurePattern");
    structPattern.def_ro("patterns", &StructurePattern::patterns);

    nb::class_<StructurePattern::FieldPattern>(structPattern, "FieldPattern")
        .def_ro("field", &StructurePattern::FieldPattern::field)
        .def_ro("pattern", &StructurePattern::FieldPattern::pattern);

    nb::class_<TimingControl>(m, "TimingControl")
        .def_ro("kind", &TimingControl::kind)
        .def_ro("syntax", &TimingControl::syntax)
        .def_ro("sourceRange", &TimingControl::sourceRange)
        .def_prop_ro("bad", &TimingControl::bad)
        .def("isEquivalentTo", &TimingControl::isEquivalentTo, "other"_a)
        .def("visit", &pyASTVisit<TimingControl>, "f"_a = nb::none(), "lookup_table"_a = nb::none(),
             PyASTVisitor::doc)
        .def("__repr__", [](const TimingControl& self) {
            return fmt::format("TimingControl(TimingControlKind.{})", toString(self.kind));
        });

    nb::class_<InvalidTimingControl, TimingControl>(m, "InvalidTimingControl");
    nb::class_<ImplicitEventControl, TimingControl>(m, "ImplicitEventControl");
    nb::class_<OneStepDelayControl, TimingControl>(m, "OneStepDelayControl");

    nb::class_<DelayControl, TimingControl>(m, "DelayControl")
        .def_prop_ro("expr", [](const DelayControl& self) { return &self.expr; });

    nb::class_<Delay3Control, TimingControl>(m, "Delay3Control")
        .def_prop_ro("expr1", [](const Delay3Control& self) { return &self.expr1; })
        .def_ro("expr2", &Delay3Control::expr2)
        .def_ro("expr3", &Delay3Control::expr3);

    nb::class_<SignalEventControl, TimingControl>(m, "SignalEventControl")
        .def_prop_ro("expr", [](const SignalEventControl& self) { return &self.expr; })
        .def_ro("iffCondition", &SignalEventControl::iffCondition)
        .def_ro("edge", &SignalEventControl::edge);

    nb::class_<EventListControl, TimingControl>(m, "EventListControl")
        .def_ro("events", &EventListControl::events);

    nb::class_<RepeatedEventControl, TimingControl>(m, "RepeatedEventControl")
        .def_prop_ro("expr", [](const RepeatedEventControl& self) { return &self.expr; })
        .def_prop_ro("event", [](const RepeatedEventControl& self) { return &self.event; });

    nb::class_<CycleDelayControl, TimingControl>(m, "CycleDelayControl")
        .def_prop_ro("expr", [](const CycleDelayControl& self) { return &self.expr; });

    nb::class_<BlockEventListControl, TimingControl> blockEventListCtrl(m, "BlockEventListControl");
    blockEventListCtrl.def_ro("events", &BlockEventListControl::events);

    nb::class_<BlockEventListControl::Event>(blockEventListCtrl, "Event")
        .def_ro("target", &BlockEventListControl::Event::target)
        .def_ro("isBegin", &BlockEventListControl::Event::isBegin);

    nb::class_<Constraint>(m, "Constraint")
        .def_ro("kind", &Constraint::kind)
        .def_ro("syntax", &Constraint::syntax)
        .def_prop_ro("bad", &Constraint::bad)
        .def("isEquivalentTo", &Constraint::isEquivalentTo, "other"_a)
        .def("__repr__", [](const Constraint& self) {
            return fmt::format("Constraint(ConstraintKind.{})", toString(self.kind));
        });

    nb::class_<InvalidConstraint, Constraint>(m, "InvalidConstraint");

    nb::class_<ConstraintList, Constraint>(m, "ConstraintList")
        .def_ro("list", &ConstraintList::list);

    nb::class_<ExpressionConstraint, Constraint>(m, "ExpressionConstraint")
        .def_ro("isSoft", &ExpressionConstraint::isSoft)
        .def_prop_ro("expr", [](const ExpressionConstraint& self) { return &self.expr; });

    nb::class_<ImplicationConstraint, Constraint>(m, "ImplicationConstraint")
        .def_prop_ro("predicate", [](const ImplicationConstraint& self) { return &self.predicate; })
        .def_prop_ro("body", [](const ImplicationConstraint& self) { return &self.body; });

    nb::class_<ConditionalConstraint, Constraint>(m, "ConditionalConstraint")
        .def_prop_ro("predicate", [](const ConditionalConstraint& self) { return &self.predicate; })
        .def_prop_ro("ifBody", [](const ConditionalConstraint& self) { return &self.ifBody; })
        .def_ro("elseBody", &ConditionalConstraint::elseBody);

    nb::class_<UniquenessConstraint, Constraint>(m, "UniquenessConstraint")
        .def_ro("items", &UniquenessConstraint::items);

    nb::class_<DisableSoftConstraint, Constraint>(m, "DisableSoftConstraint")
        .def_prop_ro("target", [](const DisableSoftConstraint& self) { return &self.target; });

    nb::class_<SolveBeforeConstraint, Constraint>(m, "SolveBeforeConstraint")
        .def_ro("solve", &SolveBeforeConstraint::solve)
        .def_ro("after", &SolveBeforeConstraint::after);

    nb::class_<ForeachConstraint, Constraint>(m, "ForeachConstraint")
        .def_prop_ro("arrayRef", [](const ForeachConstraint& self) { return &self.arrayRef; })
        .def_prop_ro("body", [](const ForeachConstraint& self) { return &self.body; })
        .def_ro("loopDims", &ForeachConstraint::loopDims);

    nb::class_<AssertionExpr>(m, "AssertionExpr")
        .def_ro("kind", &AssertionExpr::kind)
        .def_ro("syntax", &AssertionExpr::syntax)
        .def_prop_ro("bad", &AssertionExpr::bad)
        .def("isEquivalentTo", &AssertionExpr::isEquivalentTo, "other"_a)
        .def("__repr__", [](const AssertionExpr& self) {
            return fmt::format("AssertionExpr(AssertionExprKind.{})", toString(self.kind));
        });

    nb::class_<InvalidAssertionExpr, AssertionExpr>(m, "InvalidAssertionExpr");

    nb::class_<SequenceRange>(m, "SequenceRange")
        .def_ro("min", &SequenceRange::min)
        .def_ro("max", &SequenceRange::max);

    nb::class_<SequenceRepetition> seqRep(m, "SequenceRepetition");
    seqRep.def_ro("kind", &SequenceRepetition::kind).def_ro("range", &SequenceRepetition::range);

    nb::enum_<SequenceRepetition::Kind>(seqRep, "Kind")
        .value("Consecutive", SequenceRepetition::Kind::Consecutive)
        .value("Nonconsecutive", SequenceRepetition::Kind::Nonconsecutive)
        .value("GoTo", SequenceRepetition::Kind::GoTo)
        .export_values();

    nb::class_<SimpleAssertionExpr, AssertionExpr>(m, "SimpleAssertionExpr")
        .def_prop_ro("expr", [](const SimpleAssertionExpr& self) { return &self.expr; })
        .def_ro("repetition", &SimpleAssertionExpr::repetition);

    nb::class_<SequenceConcatExpr, AssertionExpr> seqConcat(m, "SequenceConcatExpr");
    seqConcat.def_ro("elements", &SequenceConcatExpr::elements);

    nb::class_<SequenceConcatExpr::Element>(seqConcat, "Element")
        .def_ro("delay", &SequenceConcatExpr::Element::delay)
        .def_ro("sequence", &SequenceConcatExpr::Element::sequence);

    nb::class_<SequenceWithMatchExpr, AssertionExpr>(m, "SequenceWithMatchExpr")
        .def_prop_ro("expr", [](const SequenceWithMatchExpr& self) { return &self.expr; })
        .def_ro("repetition", &SequenceWithMatchExpr::repetition)
        .def_ro("matchItems", &SequenceWithMatchExpr::matchItems);

    nb::class_<UnaryAssertionExpr, AssertionExpr>(m, "UnaryAssertionExpr")
        .def_prop_ro("expr", [](const UnaryAssertionExpr& self) { return &self.expr; })
        .def_ro("op", &UnaryAssertionExpr::op)
        .def_ro("range", &UnaryAssertionExpr::range);

    nb::class_<BinaryAssertionExpr, AssertionExpr>(m, "BinaryAssertionExpr")
        .def_prop_ro("left", [](const BinaryAssertionExpr& self) { return &self.left; })
        .def_prop_ro("right", [](const BinaryAssertionExpr& self) { return &self.right; })
        .def_ro("op", &BinaryAssertionExpr::op);

    nb::class_<FirstMatchAssertionExpr, AssertionExpr>(m, "FirstMatchAssertionExpr")
        .def_prop_ro("seq", [](const FirstMatchAssertionExpr& self) { return &self.seq; })
        .def_ro("matchItems", &FirstMatchAssertionExpr::matchItems);

    nb::class_<ClockingAssertionExpr, AssertionExpr>(m, "ClockingAssertionExpr")
        .def_prop_ro("clocking", [](const ClockingAssertionExpr& self) { return &self.clocking; })
        .def_prop_ro("expr", [](const ClockingAssertionExpr& self) { return &self.expr; });

    nb::class_<StrongWeakAssertionExpr, AssertionExpr> strongWeakExpr(m, "StrongWeakAssertionExpr");
    strongWeakExpr
        .def_prop_ro("expr", [](const StrongWeakAssertionExpr& self) { return &self.expr; })
        .def_ro("strength", &StrongWeakAssertionExpr::strength);

    nb::enum_<StrongWeakAssertionExpr::Strength>(strongWeakExpr, "Strength")
        .value("Strong", StrongWeakAssertionExpr::Strong)
        .value("Weak", StrongWeakAssertionExpr::Weak)
        .export_values();

    nb::class_<AbortAssertionExpr, AssertionExpr> abortExpr(m, "AbortAssertionExpr");
    abortExpr
        .def_prop_ro("condition", [](const AbortAssertionExpr& self) { return &self.condition; })
        .def_prop_ro("expr", [](const AbortAssertionExpr& self) { return &self.expr; })
        .def_ro("action", &AbortAssertionExpr::action)
        .def_ro("isSync", &AbortAssertionExpr::isSync);

    nb::enum_<AbortAssertionExpr::Action>(abortExpr, "Action")
        .value("Accept", AbortAssertionExpr::Accept)
        .value("Reject", AbortAssertionExpr::Reject)
        .export_values();

    nb::class_<ConditionalAssertionExpr, AssertionExpr>(m, "ConditionalAssertionExpr")
        .def_prop_ro("condition",
                     [](const ConditionalAssertionExpr& self) { return &self.condition; })
        .def_prop_ro("ifExpr", [](const ConditionalAssertionExpr& self) { return &self.ifExpr; })
        .def_ro("elseExpr", &ConditionalAssertionExpr::elseExpr);

    nb::class_<CaseAssertionExpr, AssertionExpr> caseAssertExpr(m, "CaseAssertionExpr");
    caseAssertExpr.def_prop_ro("expr", [](const CaseAssertionExpr& self) { return &self.expr; })
        .def_ro("items", &CaseAssertionExpr::items)
        .def_ro("defaultCase", &CaseAssertionExpr::defaultCase);

    nb::class_<CaseAssertionExpr::ItemGroup>(caseAssertExpr, "ItemGroup")
        .def_ro("expressions", &CaseAssertionExpr::ItemGroup::expressions)
        .def_ro("body", &CaseAssertionExpr::ItemGroup::body);

    nb::class_<DisableIffAssertionExpr, AssertionExpr>(m, "DisableIffAssertionExpr")
        .def_prop_ro("condition",
                     [](const DisableIffAssertionExpr& self) { return &self.condition; })
        .def_prop_ro("expr", [](const DisableIffAssertionExpr& self) { return &self.expr; });

    nb::class_<BinsSelectExpr>(m, "BinsSelectExpr")
        .def_ro("kind", &BinsSelectExpr::kind)
        .def_ro("syntax", &BinsSelectExpr::syntax)
        .def_prop_ro("bad", &BinsSelectExpr::bad)
        .def("__repr__", [](const BinsSelectExpr& self) {
            return fmt::format("BinsSelectExpr(BinsSelectExprKind.{})", toString(self.kind));
        });

    nb::class_<InvalidBinsSelectExpr, BinsSelectExpr>(m, "InvalidBinsSelectExpr");
    nb::class_<CrossIdBinsSelectExpr, BinsSelectExpr>(m, "CrossIdBinsSelectExpr");

    nb::class_<ConditionBinsSelectExpr, BinsSelectExpr>(m, "ConditionBinsSelectExpr")
        .def_prop_ro("target", [](const ConditionBinsSelectExpr& self) { return &self.target; })
        .def_ro("intersects", &ConditionBinsSelectExpr::intersects);

    nb::class_<UnaryBinsSelectExpr, BinsSelectExpr> ubse(m, "UnaryBinsSelectExpr");
    ubse.def_prop_ro("expr", [](const UnaryBinsSelectExpr& self) { return &self.expr; })
        .def_ro("op", &UnaryBinsSelectExpr::op);

    nb::enum_<UnaryBinsSelectExpr::Op>(ubse, "Op")
        .value("Negation", UnaryBinsSelectExpr::Negation)
        .export_values();

    nb::class_<BinaryBinsSelectExpr, BinsSelectExpr> bbse(m, "BinaryBinsSelectExpr");
    bbse.def_prop_ro("left", [](const BinaryBinsSelectExpr& self) { return &self.left; })
        .def_prop_ro("right", [](const BinaryBinsSelectExpr& self) { return &self.right; })
        .def_ro("op", &BinaryBinsSelectExpr::op);

    nb::enum_<BinaryBinsSelectExpr::Op>(bbse, "Op")
        .value("And", BinaryBinsSelectExpr::And)
        .value("Or", BinaryBinsSelectExpr::Or)
        .export_values();

    nb::class_<SetExprBinsSelectExpr, BinsSelectExpr>(m, "SetExprBinsSelectExpr")
        .def_prop_ro("expr", [](const SetExprBinsSelectExpr& self) { return &self.expr; })
        .def_ro("matchesExpr", &SetExprBinsSelectExpr::matchesExpr);

    nb::class_<BinSelectWithFilterExpr, BinsSelectExpr>(m, "BinSelectWithFilterExpr")
        .def_prop_ro("expr", [](const BinSelectWithFilterExpr& self) { return &self.expr; })
        .def_prop_ro("filter", [](const BinSelectWithFilterExpr& self) { return &self.filter; })
        .def_ro("matchesExpr", &BinSelectWithFilterExpr::matchesExpr);
}
