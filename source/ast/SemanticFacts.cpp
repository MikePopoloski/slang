//------------------------------------------------------------------------------
// SemanticFacts.cpp
// Semantic enums and conversion methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/SemanticFacts.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Scope.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

// clang-format off
std::optional<VariableLifetime> SemanticFacts::getVariableLifetime(Token token) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        case TokenKind::Unknown: return std::nullopt;
        default: SLANG_UNREACHABLE;
    }
}

ArgumentDirection SemanticFacts::getDirection(TokenKind kind) {
    switch (kind) {
        case TokenKind::InputKeyword: return ArgumentDirection::In;
        case TokenKind::InOutKeyword: return ArgumentDirection::InOut;
        case TokenKind::OutputKeyword: return ArgumentDirection::Out;
        case TokenKind::RefKeyword: return ArgumentDirection::Ref;
        default: SLANG_UNREACHABLE;
    }
}

ProceduralBlockKind SemanticFacts::getProceduralBlockKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AlwaysBlock: return ProceduralBlockKind::Always;
        case SyntaxKind::AlwaysCombBlock: return ProceduralBlockKind::AlwaysComb;
        case SyntaxKind::AlwaysLatchBlock: return ProceduralBlockKind::AlwaysLatch;
        case SyntaxKind::AlwaysFFBlock: return ProceduralBlockKind::AlwaysFF;
        case SyntaxKind::InitialBlock: return ProceduralBlockKind::Initial;
        case SyntaxKind::FinalBlock: return ProceduralBlockKind::Final;
        default: SLANG_UNREACHABLE;
    }
}

DefinitionKind SemanticFacts::getDefinitionKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::ModuleDeclaration: return DefinitionKind::Module;
        case SyntaxKind::InterfaceDeclaration: return DefinitionKind::Interface;
        case SyntaxKind::ProgramDeclaration: return DefinitionKind::Program;
        default: SLANG_UNREACHABLE;
    }
}

EdgeKind SemanticFacts::getEdgeKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::EdgeKeyword: return EdgeKind::BothEdges;
        case TokenKind::PosEdgeKeyword: return EdgeKind::PosEdge;
        case TokenKind::NegEdgeKeyword: return EdgeKind::NegEdge;
        default: return EdgeKind::None;
    }
}

AssertionKind SemanticFacts::getAssertKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::ImmediateAssertStatement: return AssertionKind::Assert;
        case SyntaxKind::ImmediateAssumeStatement: return AssertionKind::Assume;
        case SyntaxKind::ImmediateCoverStatement: return AssertionKind::CoverProperty;
        case SyntaxKind::AssertPropertyStatement: return AssertionKind::Assert;
        case SyntaxKind::AssumePropertyStatement: return AssertionKind::Assume;
        case SyntaxKind::CoverPropertyStatement: return AssertionKind::CoverProperty;
        case SyntaxKind::CoverSequenceStatement: return AssertionKind::CoverSequence;
        case SyntaxKind::ExpectPropertyStatement: return AssertionKind::Expect;
        case SyntaxKind::RestrictPropertyStatement: return AssertionKind::Restrict;
        default: SLANG_UNREACHABLE;
    }
}

ElabSystemTaskKind SemanticFacts::getElabSystemTaskKind(Token token) {
    auto name = token.valueText();
    if (name == "$fatal"sv)
        return ElabSystemTaskKind::Fatal;
    if (name == "$error"sv)
        return ElabSystemTaskKind::Error;
    if (name == "$warning"sv)
        return ElabSystemTaskKind::Warning;
    if (name == "$info"sv)
        return ElabSystemTaskKind::Info;
    if (name == "$static_assert"sv)
        return ElabSystemTaskKind::StaticAssert;
    SLANG_UNREACHABLE;
}

PulseStyleKind SemanticFacts::getPulseStyleKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::PulseStyleOnEventKeyword: return PulseStyleKind::OnEvent;
        case TokenKind::PulseStyleOnDetectKeyword: return PulseStyleKind::OnDetect;
        case TokenKind::ShowCancelledKeyword: return PulseStyleKind::ShowCancelled;
        case TokenKind::NoShowCancelledKeyword: return PulseStyleKind::NoShowCancelled;
        default: SLANG_UNREACHABLE;
    }
}

ChargeStrength SemanticFacts::getChargeStrength(TokenKind kind) {
    switch (kind) {
        case TokenKind::SmallKeyword: return ChargeStrength::Small;
        case TokenKind::MediumKeyword: return ChargeStrength::Medium;
        case TokenKind::LargeKeyword: return ChargeStrength::Large;
        default: SLANG_UNREACHABLE;
    }
}
// clang-format on

std::string_view SemanticFacts::getProcedureKindStr(ProceduralBlockKind kind) {
    switch (kind) {
        case ProceduralBlockKind::Initial:
            return "initial"sv;
        case ProceduralBlockKind::Final:
            return "final"sv;
        case ProceduralBlockKind::Always:
            return "always"sv;
        case ProceduralBlockKind::AlwaysComb:
            return "always_comb"sv;
        case ProceduralBlockKind::AlwaysLatch:
            return "always_latch"sv;
        case ProceduralBlockKind::AlwaysFF:
            return "always_ff"sv;
    }
    SLANG_UNREACHABLE;
}

static DriveStrength getDriveStrengthVal(TokenKind kind) {
    switch (kind) {
        case TokenKind::Supply0Keyword:
        case TokenKind::Supply1Keyword:
            return DriveStrength::Supply;
        case TokenKind::Strong0Keyword:
        case TokenKind::Strong1Keyword:
            return DriveStrength::Strong;
        case TokenKind::Weak0Keyword:
        case TokenKind::Weak1Keyword:
            return DriveStrength::Weak;
        case TokenKind::Pull0Keyword:
        case TokenKind::Pull1Keyword:
            return DriveStrength::Pull;
        case TokenKind::HighZ0Keyword:
        case TokenKind::HighZ1Keyword:
            return DriveStrength::HighZ;
        default:
            SLANG_UNREACHABLE;
    }
}

std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> SemanticFacts::
    getDriveStrength(const syntax::NetStrengthSyntax& syntax) {

    if (syntax.kind == SyntaxKind::DriveStrength) {
        auto& ds = syntax.as<DriveStrengthSyntax>();
        auto val0 = getDriveStrengthVal(ds.strength0.kind);
        auto val1 = getDriveStrengthVal(ds.strength1.kind);
        if (SyntaxFacts::isStrength0(ds.strength1.kind))
            std::swap(val0, val1);

        return {val0, val1};
    }
    else if (syntax.kind == SyntaxKind::PullStrength) {
        auto kind = syntax.as<PullStrengthSyntax>().strength.kind;
        auto val = getDriveStrengthVal(kind);
        if (SyntaxFacts::isStrength0(kind))
            return {val, {}};
        else
            return {{}, val};
    }
    else {
        return {{}, {}};
    }
}

StatementBlockKind SemanticFacts::getStatementBlockKind(const BlockStatementSyntax& syntax) {
    if (syntax.kind == SyntaxKind::SequentialBlockStatement)
        return StatementBlockKind::Sequential;

    SLANG_ASSERT(syntax.kind == SyntaxKind::ParallelBlockStatement);
    switch (syntax.end.kind) {
        case TokenKind::JoinAnyKeyword:
            return StatementBlockKind::JoinAny;
        case TokenKind::JoinNoneKeyword:
            return StatementBlockKind::JoinNone;
        default:
            return StatementBlockKind::JoinAll;
    }
}

ForwardTypeRestriction SemanticFacts::getTypeRestriction(
    syntax::ForwardTypeRestrictionSyntax& syntax) {
    switch (syntax.keyword1.kind) {
        case TokenKind::EnumKeyword:
            return ForwardTypeRestriction::Enum;
        case TokenKind::StructKeyword:
            return ForwardTypeRestriction::Struct;
        case TokenKind::UnionKeyword:
            return ForwardTypeRestriction::Union;
        case TokenKind::ClassKeyword:
            return ForwardTypeRestriction::Class;
        case TokenKind::InterfaceKeyword:
            return ForwardTypeRestriction::InterfaceClass;
        default:
            return ForwardTypeRestriction::None;
    }
}

ForwardTypeRestriction SemanticFacts::getTypeRestriction(const Type& type) {
    auto& ct = type.getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            return ForwardTypeRestriction::Struct;
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
            return ForwardTypeRestriction::Union;
        case SymbolKind::EnumType:
            return ForwardTypeRestriction::Enum;
        case SymbolKind::ClassType:
            if (ct.as<ClassType>().isInterface)
                return ForwardTypeRestriction::InterfaceClass;
            return ForwardTypeRestriction::Class;
        default:
            return ForwardTypeRestriction::None;
    }
}

std::string_view SemanticFacts::getTypeRestrictionText(ForwardTypeRestriction typeRestriction) {
    switch (typeRestriction) {
        case ForwardTypeRestriction::Enum:
            return "enum"sv;
        case ForwardTypeRestriction::Struct:
            return "struct"sv;
        case ForwardTypeRestriction::Union:
            return "union"sv;
        case ForwardTypeRestriction::Class:
            return "class"sv;
        case ForwardTypeRestriction::InterfaceClass:
            return "interface class"sv;
        default:
            return ""sv;
    }
}

void SemanticFacts::populateTimeScale(TimeScale& timeScale, const Scope& scope,
                                      const TimeUnitsDeclarationSyntax& syntax,
                                      std::optional<SourceRange>& unitsRange,
                                      std::optional<SourceRange>& precisionRange, bool isFirst) {
    bool errored = false;
    auto handle = [&](Token token, std::optional<SourceRange>& prevRange, TimeScaleValue& value) {
        // If there were syntax errors just bail out, diagnostics have already been issued.
        if (token.isMissing() || token.kind != TokenKind::TimeLiteral)
            return;

        auto val = TimeScaleValue::fromLiteral(token.realValue(), token.numericFlags().unit());
        if (!val) {
            scope.addDiag(diag::InvalidTimeScaleSpecifier, token.location());
            return;
        }

        if (prevRange) {
            // If the value was previously set, we need to make sure this new
            // value is exactly the same, otherwise we error.
            if (value != *val && !errored) {
                auto& diag = scope.addDiag(diag::MismatchedTimeScales, token.range());
                diag.addNote(diag::NotePreviousDefinition, *prevRange);
                errored = true;
            }
        }
        else {
            // The first time scale declarations must be the first elements in the parent scope.
            if (!isFirst && !errored) {
                scope.addDiag(diag::TimeScaleFirstInScope, token.range());
                errored = true;
            }

            value = *val;
            prevRange = token.range();
        }
    };

    if (syntax.keyword.kind == TokenKind::TimeUnitKeyword) {
        handle(syntax.time, unitsRange, timeScale.base);
        if (syntax.divider)
            handle(syntax.divider->value, precisionRange, timeScale.precision);
    }
    else {
        handle(syntax.time, precisionRange, timeScale.precision);
    }

    if (!errored && unitsRange && precisionRange && timeScale.precision > timeScale.base) {
        auto& diag = scope.addDiag(diag::InvalidTimeScalePrecision, *precisionRange);
        diag << *unitsRange;
    }
}

void SemanticFacts::populateTimeScale(std::optional<TimeScale>& timeScale, const Scope& scope,
                                      std::optional<TimeScale> directiveTimeScale,
                                      std::optional<SourceRange> unitsRange,
                                      std::optional<SourceRange> precisionRange) {
    // If no time unit was set, infer one based on the following rules:
    // - If the scope is nested (inside another definition), inherit from that definition.
    // - Otherwise use a `timescale directive if there is one.
    // - Otherwise, look for a time unit in the compilation scope.
    // - Finally use the compilation default.
    if (unitsRange && precisionRange)
        return;

    std::optional<TimeScale> ts;
    if (scope.asSymbol().kind == SymbolKind::CompilationUnit)
        ts = directiveTimeScale;

    if (!ts)
        ts = scope.getTimeScale();

    if (!ts) {
        // If the scope didn't have any portion of the timescale set yet,
        // then we'll just let it remain nullopt so clients know that we
        // are using the default. Otherwise we should use the built-in
        // default for the unset portion.
        if (!timeScale)
            return;

        // Defaults to 1ns/1ns
        ts.emplace();
    }
    else if (!timeScale) {
        timeScale.emplace();
    }

    if (!unitsRange)
        timeScale->base = ts->base;
    if (!precisionRange)
        timeScale->precision = ts->precision;

    if ((unitsRange || precisionRange) && timeScale->precision > timeScale->base) {
        auto range = precisionRange ? *precisionRange : *unitsRange;
        auto& diag = scope.addDiag(diag::InvalidInferredTimeScale, range);
        diag << timeScale->toString();
    }
}

bool SemanticFacts::isAllowedInModport(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Net:
        case SymbolKind::Variable:
        case SymbolKind::Subroutine:
        case SymbolKind::ClockingBlock:
            return true;
        default:
            return false;
    }
}

ClockingSkew ClockingSkew::fromSyntax(const ClockingSkewSyntax& syntax, const ASTContext& context) {
    ClockingSkew result;
    result.edge = SemanticFacts::getEdgeKind(syntax.edge.kind);

    if (syntax.delay) {
        result.delay = &TimingControl::bind(*syntax.delay, context);
        if (result.delay->kind == TimingControlKind::Delay) {
            auto cv = context.eval(result.delay->as<DelayControl>().expr);
            if (cv.isInteger())
                context.requirePositive(cv.integer(), result.delay->sourceRange);
        }
    }

    return result;
}

void ClockingSkew::serializeTo(ASTSerializer& serializer) const {
    if (edge != EdgeKind::None)
        serializer.write("edge", toString(edge));
    if (delay)
        serializer.write("delay", *delay);
}

} // namespace slang::ast
