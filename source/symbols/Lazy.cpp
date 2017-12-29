//------------------------------------------------------------------------------
// Lazy.h
// Helper types for lazy elaboration.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Lazy.h"

#include "compilation/Compilation.h"
#include "symbols/Scope.h"
#include "symbols/TypeSymbols.h"

namespace slang {

LazyInitializer::LazyInitializer(ScopeOrSymbol parent) :
    Lazy(parent, nullptr) {}

const Expression& LazyInitializer::evaluate(const Scope& scope, const ExpressionSyntax& syntax) const {
    // TODO: bind assignment-like here
    return scope.getCompilation().bindExpression(syntax, scope);
}

LazyType::LazyType(ScopeOrSymbol parent) :
    Lazy(parent, &ErrorType::Instance) {}

const Type& LazyType::evaluate(const Scope& scope, const DataTypeSyntax& syntax) const {
    return scope.getCompilation().getType(syntax, scope);
}

}