//------------------------------------------------------------------------------
// TypeSymbols.cpp
// Contains type-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

namespace slang {

static int zero = 0;
ArrayRef<int> IntegralTypeSymbol::EmptyLowerBound{ &zero, 1 };

bool isDefaultSigned(TokenKind) {
    return false;
}

bool TypeSymbol::isMatching(const TypeSymbol&) const {
    return true;
}

bool TypeSymbol::isEquivalent(const TypeSymbol& rhs) const {
    if (isMatching(rhs))
        return true;

    return true;
}

bool TypeSymbol::isAssignmentCompatible(const TypeSymbol& rhs) const {
    if (isEquivalent(rhs))
        return true;

    return true;
}

bool TypeSymbol::isCastCompatible(const TypeSymbol& rhs) const {
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
            /*case SymbolKind::Instance: {
            result = name.toString();
            auto ia = as<InstanceSymbol>();
            for (auto r : ia.dimensions)
            result += "[" + r.left.toString(LiteralBase::Decimal) +
            ":" + r.right.toString(LiteralBase::Decimal) + "]";
            break;
            }*/
        default:
            break;
    }
    return "'" + result + "'";
}

bool TypeSymbol::isSigned() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().isSigned;
        case SymbolKind::RealType: return true;
        default: return false;
    }
}

bool TypeSymbol::isFourState() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().isFourState;
        case SymbolKind::RealType: return false;
        default: return false;
    }
}

bool TypeSymbol::isReal() const {
    switch (kind) {
        case SymbolKind::IntegralType: return false;
        case SymbolKind::RealType: return true;
        default: return false;
    }
}

int TypeSymbol::width() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().width;
        case SymbolKind::RealType: return as<RealTypeSymbol>().width;
        default: return 0;
    }
}

}
