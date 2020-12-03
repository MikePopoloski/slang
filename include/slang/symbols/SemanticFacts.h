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

class Scope;
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

#define ASK(x) x(Assert) x(Assume) x(Cover)
/// Specifies possible assertion kinds.
ENUM(AssertionKind, ASK);
#undef ASK

// clang-format off
#define GATE(x) \
    x(Cmos) \
    x(Rcmos) \
    x(Nmos) \
    x(Pmos) \
    x(Rnmos) \
    x(Rpmos) \
    x(BufIf0) \
    x(BufIf1) \
    x(NotIf0) \
    x(NotIf1) \
    x(And) \
    x(Nand) \
    x(Or) \
    x(Nor) \
    x(Xor) \
    x(Xnor) \
    x(Buf) \
    x(Not) \
    x(TranIf0) \
    x(TranIf1) \
    x(RtranIf0) \
    x(RtranIf1) \
    x(Tran) \
    x(Rtran) \
    x(PullDown) \
    x(PullUp)
// clang-format on

ENUM(GateType, GATE)
#undef GATE

#define ELAB(x) x(Fatal) x(Error) x(Warning) x(Info)
/// Specifies possible elaboration system task kinds.
ENUM(ElabSystemTaskKind, ELAB);
#undef ELAB

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

    static GateType getGateType(TokenKind kind);

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

} // namespace slang
