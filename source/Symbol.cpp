#include "Symbol.h"

namespace slang {

bool isDefaultSigned(TokenKind kind) {
    return false;
}

bool TypeSymbol::isIntegral() const {
    switch (kind) {
        case SymbolKind::IntegralType:
        case SymbolKind::VectorIntegralType:
            return true;
        default:
            return false;
    }
}

std::string TypeSymbol::toString() const {
    std::string result;
    switch (kind) {
        case SymbolKind::IntegralType: {
            const auto& s = as<IntegralTypeSymbol>();
            result = name.toString();
            if (isDefaultSigned(s.keywordType) != s.isSigned)
                result += s.isSigned ? " signed" : " unsigned";
            break;
        }
        case SymbolKind::RealType:
            result = name.toString();
            break;
        default:
            break;
    }
    return "'" + result + "'";
}

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