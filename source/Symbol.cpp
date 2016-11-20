#include "Symbol.h"

namespace slang {

ParameterSymbol::ParameterSymbol(StringRef name, SourceLocation location,
                                 const ParameterDeclarationSyntax* syntax,
                                 const ExpressionSyntax* initializer, bool isLocal) :
    Symbol(SymbolKind::Parameter, name, location),
    syntax(syntax),
    initializer(initializer),
    isLocal(isLocal)
{
}

}