//------------------------------------------------------------------------------
//! @file SemanticFacts.h
//! @brief Semantic enums and conversion methods
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <optional>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"

namespace slang {

class ASTSerializer;
class BindContext;
class Scope;
class TimingControl;
enum class SymbolKind;
struct BlockStatementSyntax;
struct TimeUnitsDeclarationSyntax;

#define LIFETIME(x) x(Automatic) x(Static)
/// Specifies the storage lifetime of a variable.
ENUM(VariableLifetime, LIFETIME);
#undef LIFETIME

#define VISIBILITY(x) x(Public) x(Protected) x(Local)
/// Specifies the visibility of class members.
ENUM(Visibility, VISIBILITY);
#undef VISIBILITY

#define DIRECTION(x) x(In) x(Out) x(InOut) x(Ref)
/// Specifies behavior of an argument passed to a subroutine.
ENUM(ArgumentDirection, DIRECTION);
#undef DIRECTION

#define BLOCK(x) x(Initial) x(Final) x(Always) x(AlwaysComb) x(AlwaysLatch) x(AlwaysFF)
/// Specifies possible procedural block kinds.
ENUM(ProceduralBlockKind, BLOCK);
#undef BLOCK

#define BLOCK(x) x(Sequential) x(JoinAll) x(JoinAny) x(JoinNone)
/// Specifies possible statement block kinds.
ENUM(StatementBlockKind, BLOCK);
#undef BLOCK

#define DEF(x) x(Module) x(Interface) x(Program)
/// Specifies possible definition kinds.
ENUM(DefinitionKind, DEF);
#undef DEF

#define UD(x) x(None) x(Pull0) x(Pull1)
/// Specifies possible unconnected drive settings.
ENUM(UnconnectedDrive, UD);
#undef UD

#define EDGE(x) x(None) x(PosEdge) x(NegEdge) x(BothEdges)
/// Specifies possible edge kinds.
ENUM(EdgeKind, EDGE);
#undef EDGE

#define SRK(x) x(Function) x(Task)
/// Specifies possible subroutine kinds.
ENUM(SubroutineKind, SRK);
#undef SRK

#define ASK(x) x(Assert) x(Assume) x(CoverProperty) x(CoverSequence) x(Restrict) x(Expect)
/// Specifies possible assertion kinds.
ENUM(AssertionKind, ASK);
#undef ASK

#define ELAB(x) x(Fatal) x(Error) x(Warning) x(Info)
/// Specifies possible elaboration system task kinds.
ENUM(ElabSystemTaskKind, ELAB);
#undef ELAB

#define MODE(x) x(None) x(Rand) x(RandC)
/// Specifies possible assertion kinds.
ENUM(RandMode, MODE);
#undef MODE

#define DIRECTION(x) x(In) x(Out) x(OutReg) x(InOut)
/// Specifies behavior of a primitive port.
ENUM(PrimitivePortDirection, DIRECTION);
#undef DIRECTION

class SemanticFacts {
public:
    /// Interprets a keyword token as a variable lifetime value.
    static std::optional<VariableLifetime> getVariableLifetime(Token token);

    /// Interprets a token type as an argument direction value.
    static ArgumentDirection getDirection(TokenKind kind);

    static ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind);

    static DefinitionKind getDefinitionKind(SyntaxKind kind);

    static EdgeKind getEdgeKind(TokenKind kind);

    static AssertionKind getAssertKind(SyntaxKind kind);

    static StatementBlockKind getStatementBlockKind(const BlockStatementSyntax& syntax);

    static ElabSystemTaskKind getElabSystemTaskKind(Token token);

    static void populateTimeScale(TimeScale& timeScale, const Scope& scope,
                                  const TimeUnitsDeclarationSyntax& syntax,
                                  optional<SourceRange>& unitsRange,
                                  optional<SourceRange>& precisionRange, bool isFirst);

    static void populateTimeScale(TimeScale& timeScale, const Scope& scope,
                                  optional<TimeScale> directiveTimeScale, bool hasBase,
                                  bool hasPrecision);

    static bool isAllowedInModport(SymbolKind kind);

private:
    SemanticFacts() = default;
};

struct ClockingSkewSyntax;

/// Represents a skew value that is applied to clocking block signals.
class ClockingSkew {
public:
    /// The edge on which the signal should be sampled.
    EdgeKind edge = EdgeKind::None;

    /// An optional delay to apply when sampling the signal.
    const TimingControl* delay = nullptr;

    /// Returns true if any explicit skew information is specified; this method
    /// will return false on a default constructed object.
    bool hasValue() const { return delay || edge != EdgeKind::None; }

    void serializeTo(ASTSerializer& serializer) const;

    static ClockingSkew fromSyntax(const ClockingSkewSyntax& syntax, const BindContext& context);
};

} // namespace slang
