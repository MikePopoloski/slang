#include "Symbol.h"

namespace slang {

constexpr SymbolKind Symbol                ::mykind;
constexpr SymbolKind TypeSymbol            ::mykind;
constexpr SymbolKind IntegralTypeSymbol    ::mykind;
constexpr SymbolKind RealTypeSymbol        ::mykind;
constexpr SymbolKind EnumTypeSymbol        ::mykind;
constexpr SymbolKind StructTypeSymbol      ::mykind;
constexpr SymbolKind ErrorTypeSymbol       ::mykind;
constexpr SymbolKind TypeAliasSymbol       ::mykind;
constexpr SymbolKind AttributeSymbol       ::mykind;
constexpr SymbolKind ParameterSymbol       ::mykind;
constexpr SymbolKind ModuleSymbol          ::mykind;
constexpr SymbolKind InstanceSymbol        ::mykind;
constexpr SymbolKind GenerateBlock         ::mykind;

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

AttributeSymbol::AttributeSymbol(const AttributeSpecSyntax* syntax, const TypeSymbol* type, ConstantValue value) :
    Symbol(SymbolKind::Attribute, syntax->name.valueText(), syntax->name.location()),
    syntax(syntax), type(type), value(value)
{
}

ParameterSymbol::ParameterSymbol(StringRef name, SourceLocation location,
                                 const ParameterDeclarationSyntax* syntax,
                                 bool isLocal) :
    Symbol(SymbolKind::Parameter, name, location),
    syntax(syntax),
    isLocal(isLocal),
    // TODO: fill this in with something meaningful
    // this is to prevent it from being uninitialized memory
    type(new TypeSymbol(SymbolKind::Unknown,name,location))
{
}

}
