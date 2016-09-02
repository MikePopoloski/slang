#pragma once

#include "AllSyntax.h"
#include "BoundNodes.h"

namespace slang {

// Handles binding syntax nodes into symbols and bound trees (for expressions).
// The binder maintains context (like in a specific scope) and knows about parent
// contexts so that symbol lookup can be performed.
class Binder {
    BoundExpression* bindExpression(ExpressionSyntax* syntax);
};

}