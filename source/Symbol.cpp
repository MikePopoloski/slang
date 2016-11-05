#include "Symbol.h"

namespace slang {

DesignElementSymbol::DesignElementSymbol(const ModuleDeclarationSyntax* syntax, ArrayRef<ParameterSymbol*> parameters) :
	Symbol(syntax->header->name.valueText(), syntax->header->name.location()),
	syntax(syntax), parameters(parameters)
{
}

}