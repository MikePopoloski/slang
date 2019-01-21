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

namespace slang {

#define LIFETIME(x) x(Automatic) x(Static)
/// Specifies the storage lifetime of a variable.
ENUM(VariableLifetime, LIFETIME);
#undef LIFETIME

#define FORMAL(x) x(In) x(Out) x(InOut) x(Ref) x(ConstRef)
/// Specifies behavior of an argument passed to a subroutine.
ENUM(FormalArgumentDirection, FORMAL);
#undef FORMAL

#define BLOCK(x) x(Initial) x(Final) x(Always) x(AlwaysComb) x(AlwaysLatch) x(AlwaysFF)
/// Specifies possible procedural block kinds.
ENUM(ProceduralBlockKind, BLOCK);
#undef BLOCK

#define PORT(x) x(NotApplicable) x(In) x(Out) x(InOut) x(Ref)
/// Specifies the behavior of connections to a particular port.
ENUM(PortDirection, PORT);
#undef PORT

#define DEF(x) x(Module) x(Interface) x(Program)
/// Specifies possible definition kinds.
ENUM(DefinitionKind, DEF);
#undef DEF

namespace SemanticFacts {

/// Interprets a keyword token as a variable lifetime value.
std::optional<VariableLifetime> getVariableLifetime(Token token);

/// Interprets a token type as a port direction value.
PortDirection getPortDirection(TokenKind kind);

ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind);

DefinitionKind getDefinitionKind(SyntaxKind kind);

} // namespace SemanticFacts

} // namespace slang
