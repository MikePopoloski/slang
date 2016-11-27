#include "Symbol.h"

namespace slang {

static int zero = 0;
ArrayRef<int> IntegralTypeSymbol::EmptyLowerBound { &zero, 1 };

bool isDefaultSigned(TokenKind kind) {
    return false;
}

bool TypeSymbol::isMatching(const TypeSymbol* rhs) const {
    return true;
}

bool TypeSymbol::isEquivalent(const TypeSymbol* rhs) const {
    if (isMatching(rhs))
        return true;

    return true;
}

bool TypeSymbol::isAssignmentCompatible(const TypeSymbol* rhs) const {
    if (isEquivalent(rhs))
        return true;

    return true;
}

bool TypeSymbol::isCastCompatible(const TypeSymbol* rhs) const {
    if (isAssignmentCompatible(rhs))
        return true;

    return true;
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