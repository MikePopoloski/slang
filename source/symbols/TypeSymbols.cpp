//------------------------------------------------------------------------------
// TypeSymbols.cpp
// Contains type-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "TypeSymbols.h"

#include "compilation/Compilation.h"

namespace slang {

const ErrorTypeSymbol ErrorTypeSymbol::Instance;

static int zero = 0;
span<int const> IntegralTypeSymbol::EmptyLowerBound{ &zero, 1 };

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
            result = name;
            if (isDefaultSigned(s.keywordType) != s.isSigned)
                result += s.isSigned ? " signed" : " unsigned";
            break;
        }
        case SymbolKind::RealType:
            result = name;
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


const TypeSymbol& IntegralTypeSymbol::fromSyntax(Compilation& compilation,
                                                 const IntegerTypeSyntax& syntax,
                                                 const Scope& scope) {
    // This is a simple integral vector (possibly of just one element).
    bool isReg = syntax.keyword.kind == TokenKind::RegKeyword;
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = syntax.kind != SyntaxKind::BitType;

    SmallVectorSized<ConstantRange, 4> dims;
    if (!evaluateConstantDims(syntax.dimensions, dims, scope))
        return compilation.getErrorType();

    // TODO: review this whole mess

    if (dims.empty()) {
        // TODO: signing
        return compilation.getType(syntax.kind);
    }
    else if (dims.size() == 1 && dims[0].right == 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        int width = dims[0].left + 1;
        return compilation.getType(width, isSigned, isFourState, isReg);
    }
    else {
        SmallVectorSized<int, 4> lowerBounds;
        SmallVectorSized<int, 4> widths;
        int totalWidth = 0;
        for (auto& dim : dims) {
            int msb = dim.left;
            int lsb = dim.right;
            int width;
            if (msb > lsb) {
                width = msb - lsb + 1;
                lowerBounds.append(lsb);
            }
            else {
                // TODO: msb == lsb
                width = lsb - msb + 1;
                lowerBounds.append(-lsb);
            }
            widths.append(width);

            // TODO: overflow
            totalWidth += width;
        }
        return compilation.getType(totalWidth, isSigned, isFourState, isReg,
                                   lowerBounds.copy(compilation), widths.copy(compilation));
    }
}

bool IntegralTypeSymbol::evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const Scope& scope) {
    for (const VariableDimensionSyntax* dim : dimensions) {
        const SelectorSyntax* selector;
        if (!dim->specifier || dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier ||
            (selector = &dim->specifier->as<RangeDimensionSpecifierSyntax>().selector)->kind != SyntaxKind::SimpleRangeSelect) {

            // TODO: errors
            //auto& diag = addError(DiagCode::PackedDimRequiresConstantRange, dim->specifier->getFirstToken().location());
            //diag << dim->specifier->sourceRange();
            return false;
        }

        const RangeSelectSyntax& range = selector->as<RangeSelectSyntax>();

        // §6.9.1 - Implementations may set a limit on the maximum length of a vector, but the limit shall be at least 65536 (2^16) bits.
        const int MaxRangeBits = 16;

        // TODO: errors
        auto left = scope.evaluateConstant(range.left).coerceInteger(MaxRangeBits);
        auto right = scope.evaluateConstant(range.right).coerceInteger(MaxRangeBits);

        if (!left || !right)
            return false;

        results.emplace(ConstantRange{ *left, *right });
    }
    return true;
}

}
