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

/// Indicates which built-in system function is represented by a symbol.
enum class SystemFunction {
    Unknown,
    clog2,
    bits,
    left,
    right,
    low,
    high,
    size,
    increment
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

namespace SemanticFacts {

/// Interprets a keyword token as a variable lifetime value.
std::optional<VariableLifetime> getVariableLifetime(Token token);

ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind);

}

}
