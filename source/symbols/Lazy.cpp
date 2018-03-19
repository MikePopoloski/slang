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
    const ValueSymbol& value = getSymbol().as<ValueSymbol>();
    return Expression::bind(scope.getCompilation(), value.getType(), syntax,
                            SourceLocation(), // TODO: set real source location
                            BindContext(scope, LookupLocation::before(value)));
}

LazyType::LazyType(ScopeOrSymbol parent) :
    Lazy(parent, &ErrorType::Instance) {}

const Type& LazyType::evaluate(const Scope& scope, const DataTypeSyntax& syntax) const {
    return scope.getCompilation().getType(syntax, LookupLocation::before(getSymbol()), scope);
}

}