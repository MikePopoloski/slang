//------------------------------------------------------------------------------
//! @file SemanticFacts.h
//! @brief Semantic enums and conversion methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/syntax/SyntaxNode.h"

namespace slang::ast {

class ASTSerializer;
class ASTContext;
class Scope;
class TimingControl;
class Type;
enum class SymbolKind;

#define LIFETIME(x) x(Automatic) x(Static)
SLANG_ENUM(VariableLifetime, LIFETIME)
#undef LIFETIME

#define VISIBILITY(x) x(Public) x(Protected) x(Local)
SLANG_ENUM(Visibility, VISIBILITY)
#undef VISIBILITY

#define DIRECTION(x) x(In) x(Out) x(InOut) x(Ref)
SLANG_ENUM(ArgumentDirection, DIRECTION)
#undef DIRECTION

#define BLOCK(x) x(Initial) x(Final) x(Always) x(AlwaysComb) x(AlwaysLatch) x(AlwaysFF)
SLANG_ENUM(ProceduralBlockKind, BLOCK)
#undef BLOCK

#define BLOCK(x) x(Sequential) x(JoinAll) x(JoinAny) x(JoinNone)
SLANG_ENUM(StatementBlockKind, BLOCK)
#undef BLOCK

#define DEF(x) x(Module) x(Interface) x(Program)
SLANG_ENUM(DefinitionKind, DEF)
#undef DEF

#define UD(x) x(None) x(Pull0) x(Pull1)
SLANG_ENUM(UnconnectedDrive, UD)
#undef UD

#define EDGE(x) x(None) x(PosEdge) x(NegEdge) x(BothEdges)
SLANG_ENUM(EdgeKind, EDGE)
#undef EDGE

#define SRK(x) x(Function) x(Task)
SLANG_ENUM(SubroutineKind, SRK)
#undef SRK

#define ASK(x) x(Assert) x(Assume) x(CoverProperty) x(CoverSequence) x(Restrict) x(Expect)
SLANG_ENUM(AssertionKind, ASK)
#undef ASK

#define ELAB(x) x(Fatal) x(Error) x(Warning) x(Info) x(StaticAssert)
SLANG_ENUM(ElabSystemTaskKind, ELAB)
#undef ELAB

#define MODE(x) x(None) x(Rand) x(RandC)
SLANG_ENUM(RandMode, MODE)
#undef MODE

#define DIRECTION(x) x(In) x(Out) x(OutReg) x(InOut)
SLANG_ENUM(PrimitivePortDirection, DIRECTION)
#undef DIRECTION

#define PSK(x) x(OnEvent) x(OnDetect) x(ShowCancelled) x(NoShowCancelled)
SLANG_ENUM(PulseStyleKind, PSK)
#undef PSK

#define CS(x) x(Small) x(Medium) x(Large)
SLANG_ENUM(ChargeStrength, CS)
#undef CS

#define DS(x) x(Supply) x(Strong) x(Pull) x(Weak) x(HighZ)
SLANG_ENUM(DriveStrength, DS)
#undef DS

#define FTR(x) x(None) x(Enum) x(Struct) x(Union) x(Class) x(InterfaceClass)
SLANG_ENUM(ForwardTypeRestriction, FTR)
#undef FTR

#define CASE_CONDITION(x) x(Normal) x(WildcardXOrZ) x(WildcardJustZ) x(Inside)
SLANG_ENUM(CaseStatementCondition, CASE_CONDITION)
#undef CASE_CONDITION

/// A set of flags that control how assignments are checked.
enum class SLANG_EXPORT AssignFlags : uint8_t {
    /// No special assignment behavior specified.
    None = 0,

    /// The assignment is non-blocking.
    NonBlocking = 1 << 0,

    /// The assignment is occurring inside a concatenation.
    InConcat = 1 << 1,

    /// The assignment is for an inout port of a module / interface / program.
    InOutPort = 1 << 2
};
SLANG_BITMASK(AssignFlags, InOutPort)

/// A helper class that can extract semantic AST information from
/// tokens and syntax nodes.
class SLANG_EXPORT SemanticFacts {
public:
    /// Interprets a keyword token as a variable lifetime value.
    static std::optional<VariableLifetime> getVariableLifetime(parsing::Token token);

    /// Interprets a token type as an argument direction value.
    static ArgumentDirection getDirection(parsing::TokenKind kind);

    /// Interprets a syntax kind as a procedural block kind.
    static ProceduralBlockKind getProceduralBlockKind(syntax::SyntaxKind kind);

    /// Interprets a syntax kind as a definition kind.
    static DefinitionKind getDefinitionKind(syntax::SyntaxKind kind);

    /// Interprets an edge token as an EdgeKind value.
    static EdgeKind getEdgeKind(parsing::TokenKind kind);

    /// Interprets a syntax kind as an assertion kind.
    static AssertionKind getAssertKind(syntax::SyntaxKind kind);

    /// Gets the statement block kind from the given syntax node.
    static StatementBlockKind getStatementBlockKind(const syntax::BlockStatementSyntax& syntax);

    /// Interprets a system name token as an elaboration system task kind.
    static ElabSystemTaskKind getElabSystemTaskKind(parsing::Token token);

    /// Interprets a token type as a pulse style kind.
    static PulseStyleKind getPulseStyleKind(parsing::TokenKind kind);

    /// Interprets a token type as a charge strength.
    static ChargeStrength getChargeStrength(parsing::TokenKind kind);

    /// Gets the human-friendly string name of a procedural block kind.
    static std::string_view getProcedureKindStr(ProceduralBlockKind kind);

    /// Gets a human-friendly string name of a case statement condition kind.
    static std::string_view getCaseConditionStr(CaseStatementCondition kind);

    /// Gets the optional drive strength values associated with the given net strength syntax node.
    static std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> getDriveStrength(
        const syntax::NetStrengthSyntax& syntax);

    /// Gets the forward type restriction associated with the given syntax node.
    static ForwardTypeRestriction getTypeRestriction(syntax::ForwardTypeRestrictionSyntax& syntax);

    /// Gets the forward type restriction that matches the given type.
    static ForwardTypeRestriction getTypeRestriction(const Type& type);

    /// Gets the human-friendly string name of the given forward type restriction kind.
    static std::string_view getTypeRestrictionText(ForwardTypeRestriction typeRestriction);

    /// Populates the given timescale object with the appropriate values specified by
    /// the given syntax node. Reports errors if needed.
    static void populateTimeScale(TimeScale& timeScale, const Scope& scope,
                                  const syntax::TimeUnitsDeclarationSyntax& syntax,
                                  std::optional<SourceRange>& unitsRange,
                                  std::optional<SourceRange>& precisionRange, bool isFirst);

    /// Populates the given timescale object with the given values.
    /// Reports errors if the timescale is invalid.
    static void populateTimeScale(std::optional<TimeScale>& timeScale, const Scope& scope,
                                  std::optional<TimeScale> directiveTimeScale,
                                  std::optional<SourceRange> unitsRange,
                                  std::optional<SourceRange> precisionRange);

    /// @returns true if the given symbol kind is allowed in modports.
    static bool isAllowedInModport(SymbolKind kind);

    /// @returns true if the given system name is a global future sampled value function.
    static bool isGlobalFutureSampledValueFunc(parsing::KnownSystemName name);

private:
    SemanticFacts() = default;
};

/// Represents a skew value that is applied to clocking block signals.
class SLANG_EXPORT ClockingSkew {
public:
    /// The edge on which the signal should be sampled.
    EdgeKind edge = EdgeKind::None;

    /// An optional delay to apply when sampling the signal.
    const TimingControl* delay = nullptr;

    /// Returns true if any explicit skew information is specified; this method
    /// will return false on a default constructed object.
    bool hasValue() const { return delay || edge != EdgeKind::None; }

    void serializeTo(ASTSerializer& serializer) const;

    static ClockingSkew fromSyntax(const syntax::ClockingSkewSyntax& syntax,
                                   const ASTContext& context);
};

} // namespace slang::ast
