//------------------------------------------------------------------------------
// SemanticFacts.h
// Semantic enums and conversion methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <optional>

#include "lexing/Token.h"
#include "parsing/SyntaxNode.h"

namespace slang {

/// Specifies the storage lifetime of a variable.
enum class VariableLifetime {
    Automatic,
    Static
};

/// Specifies behavior of an argument passed to a subroutine.
enum class FormalArgumentDirection {
    In,
    Out,
    InOut,
    Ref,
    ConstRef
};

/// Specifies possible procedural block kinds.
enum class ProceduralBlockKind {
    Initial,
    Final,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFF
};

/// Specifies possible port kinds.
enum class PortKind {
    Net,
    Variable,
    Explicit,
    Interconnect,
    Interface
};

/// Specifies the behavior of connections to a particular port.
enum class PortDirection {
    NotApplicable,
    In,
    Out,
    InOut,
    Ref
};

namespace SemanticFacts {

/// Interprets a keyword token as a variable lifetime value.
std::optional<VariableLifetime> getVariableLifetime(Token token);

/// Interprets a token type as a port direction value.
PortDirection getPortDirection(TokenKind kind);

ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind);

}

}
