//------------------------------------------------------------------------------
// ValueSymbol.cpp
// Base class for all value symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/ValueSymbol.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/Scope.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

ValueSymbol::ValueSymbol(SymbolKind kind, std::string_view name, SourceLocation location,
                         bitmask<DeclaredTypeFlags> flags) :
    Symbol(kind, name, location), declaredType(*this, flags) {
}

void ValueSymbol::setFromDeclarator(const DeclaratorSyntax& decl) {
    declaredType.setFromDeclarator(decl);
    setSyntax(decl);
}

bool ValueSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::Net:
        case SymbolKind::EnumValue:
        case SymbolKind::Parameter:
        case SymbolKind::PrimitivePort:
        case SymbolKind::ModportPort:
        case SymbolKind::Specparam:
            return true;
        default:
            return VariableSymbol::isKind(kind);
    }
}

void ValueSymbol::addDriver(DriverKind driverKind, const Expression& longestStaticPrefix,
                            const Symbol& containingSymbol, bitmask<AssignFlags> flags) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    EvalContext evalCtx(ASTContext(*scope, LookupLocation::max));

    auto bounds = ValueDriver::getBounds(longestStaticPrefix, evalCtx, getType());
    if (!bounds)
        return;

    comp.emplace<ValueDriver>(driverKind, longestStaticPrefix, containingSymbol, flags);
    // addDriver(*bounds, *driver);
}

void ValueSymbol::addDriver(DriverKind driverKind, DriverBitRange,
                            const Expression& longestStaticPrefix, const Symbol& containingSymbol,
                            const Expression& procCallExpression) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto driver = comp.emplace<ValueDriver>(driverKind, longestStaticPrefix, containingSymbol,
                                            AssignFlags::None);
    driver->procCallExpression = &procCallExpression;

    // addDriver(bounds, *driver);
}

void ValueSymbol::addDriverFromSideEffect(const ValueDriver& newDriver) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    EvalContext evalCtx(ASTContext(*scope, LookupLocation::max));
    auto bounds = ValueDriver::getBounds(*newDriver.prefixExpression, evalCtx, getType());
    if (!bounds)
        return;

    // addDriver(*bounds, newDriver);
}

template<typename TCallback>
static void visitPrefixExpressions(const Expression& longestStaticPrefix, bool includeRoot,
                                   TCallback&& callback) {
    auto expr = &longestStaticPrefix;
    do {
        switch (expr->kind) {
            case ExpressionKind::NamedValue:
            case ExpressionKind::HierarchicalValue:
            case ExpressionKind::Call:
                if (includeRoot)
                    callback(*expr);
                expr = nullptr;
                break;
            case ExpressionKind::Conversion:
                expr = &expr->as<ConversionExpression>().operand();
                break;
            case ExpressionKind::ElementSelect:
                callback(*expr);
                expr = &expr->as<ElementSelectExpression>().value();
                break;
            case ExpressionKind::RangeSelect:
                callback(*expr);
                expr = &expr->as<RangeSelectExpression>().value();
                break;
            case ExpressionKind::MemberAccess: {
                auto& access = expr->as<MemberAccessExpression>();
                if (access.member.kind == SymbolKind::Field) {
                    callback(*expr);
                    expr = &access.value();
                }
                else {
                    expr = nullptr;
                }
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }
    } while (expr);
}

void ValueSymbol::addPortBackref(const PortSymbol& port) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    firstPortBackref = comp.emplace<PortBackref>(port, firstPortBackref);
}

ValueDriver::ValueDriver(DriverKind kind, const Expression& longestStaticPrefix,
                         const Symbol& containingSymbol, bitmask<AssignFlags> flags) :
    prefixExpression(&longestStaticPrefix), containingSymbol(&containingSymbol), flags(flags),
    kind(kind) {

    if (containingSymbol.kind == SymbolKind::ProceduralBlock) {
        source = static_cast<DriverSource>(
            containingSymbol.as<ProceduralBlockSymbol>().procedureKind);
    }
    else if (containingSymbol.kind == SymbolKind::Subroutine) {
        source = DriverSource::Subroutine;
    }
    else {
        source = DriverSource::Other;
    }
}

SourceRange ValueDriver::getSourceRange() const {
    if (procCallExpression)
        return procCallExpression->sourceRange;
    return prefixExpression->sourceRange;
}

std::optional<DriverBitRange> ValueDriver::getBounds(const Expression& prefixExpression,
                                                     EvalContext& evalContext,
                                                     const Type& rootType) {
    auto type = &rootType.getCanonicalType();
    DriverBitRange result{0, type->getSelectableWidth() - 1};

    SmallVector<const Expression*> path;
    visitPrefixExpressions(prefixExpression, /* includeRoot */ false,
                           [&](const Expression& expr) { path.push_back(&expr); });

    for (size_t i = path.size(); i > 0; i--) {
        uint64_t start, width;
        auto& elem = *path[i - 1];
        if (elem.kind == ExpressionKind::MemberAccess) {
            auto& member = elem.as<MemberAccessExpression>().member;
            if (member.kind != SymbolKind::Field)
                return std::nullopt;

            auto& field = member.as<FieldSymbol>();
            start = field.bitOffset;
            width = elem.type->getSelectableWidth();
        }
        else {
            auto elemRange = elem.evalSelector(evalContext, /* enforceBounds */ true);
            if (!elemRange)
                return std::nullopt;

            SLANG_ASSERT(elemRange->left >= 0 && elemRange->right >= 0);
            start = (uint64_t)elemRange->lower();
            width = elemRange->width();
        }

        if (type->kind == SymbolKind::FixedSizeUnpackedArrayType) {
            // Unpacked arrays need their selection adjusted since they
            // return a simple index instead of a bit offset.
            type = &type->getArrayElementType()->getCanonicalType();
            uint64_t elemWidth = type->getSelectableWidth();
            result.first += start * elemWidth;
            result.second = result.first + elemWidth - 1;
        }
        else {
            type = &elem.type->getCanonicalType();
            result.first += start;
            result.second = result.first + width - 1;
        }
    }

    return result;
}

} // namespace slang::ast
