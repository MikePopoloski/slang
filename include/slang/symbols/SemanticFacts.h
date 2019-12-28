//------------------------------------------------------------------------------
// SemanticFacts.h
// Semantic enums and conversion methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <optional>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/Enum.h"

namespace slang {

struct BlockStatementSyntax;

#define LIFETIME(x) x(Automatic) x(Static)
/// Specifies the storage lifetime of a variable.
ENUM(VariableLifetime, LIFETIME);
#undef LIFETIME

#define FORMAL(x) x(In) x(Out) x(InOut) x(Ref) x(ConstRef)
/// Specifies behavior of an argument passed to a subroutine.
ENUM(ArgumentDirection, FORMAL);
#undef FORMAL

#define BLOCK(x) x(Initial) x(Final) x(Always) x(AlwaysComb) x(AlwaysLatch) x(AlwaysFF)
/// Specifies possible procedural block kinds.
ENUM(ProceduralBlockKind, BLOCK);
#undef BLOCK

#define BLOCK(x) x(Sequential) x(JoinAll) x(JoinAny) x(JoinNone)
/// Specifies possible statement block kinds.
ENUM(StatementBlockKind, BLOCK);
#undef BLOCK

#define PORT(x) x(In) x(Out) x(InOut) x(Ref)
/// Specifies the behavior of connections to a particular port.
ENUM(PortDirection, PORT);
#undef PORT

#define DEF(x) x(Module) x(Interface) x(Program)
/// Specifies possible definition kinds.
ENUM(DefinitionKind, DEF);
#undef DEF

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

namespace SemanticFacts {

/// Interprets a keyword token as a variable lifetime value.
std::optional<VariableLifetime> getVariableLifetime(Token token);

/// Interprets a token type as a port direction value.
PortDirection getPortDirection(TokenKind kind);

ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind);

DefinitionKind getDefinitionKind(SyntaxKind kind);

EdgeKind getEdgeKind(TokenKind kind);

AssertionKind getAssertKind(SyntaxKind kind);

StatementBlockKind getStatementBlockKind(const BlockStatementSyntax& syntax);

ArgumentDirection getArgDirection(PortDirection direction);

} // namespace SemanticFacts

} // namespace slang
