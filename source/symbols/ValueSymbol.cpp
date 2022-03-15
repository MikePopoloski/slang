//------------------------------------------------------------------------------
// ValueSymbol.cpp
// Base class for all value symbols
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ValueSymbol.h"

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/Expression.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/SelectExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/NetType.h"

namespace slang {

ValueSymbol::ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                         bitmask<DeclaredTypeFlags> flags) :
    Symbol(kind, name, location),
    declaredType(*this, flags) {
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

ValueSymbol::Driver::Driver(DriverKind kind, const Expression& longestStaticPrefix) :
    longestStaticPrefix(&longestStaticPrefix), kind(kind) {
}

static const Expression* nextPrefix(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            return nullptr;
        case ExpressionKind::ElementSelect:
            return &expr.as<ElementSelectExpression>().value();
        case ExpressionKind::RangeSelect:
            return &expr.as<RangeSelectExpression>().value();
        case ExpressionKind::MemberAccess:
            return &expr.as<MemberAccessExpression>().value();
        default:
            THROW_UNREACHABLE;
    }
}

static bool prefixOverlaps(EvalContext& ctx, const Expression& left, const Expression& right) {
    // A named value here should always point to the same symbol,
    // so we only need to check if they have the same expression kind.
    if (ValueExpressionBase::isKind(left.kind) && ValueExpressionBase::isKind(right.kind))
        return true;

    auto getRange = [&ctx](const Expression& expr) -> optional<ConstantRange> {
        ConstantValue unused;
        if (expr.kind == ExpressionKind::ElementSelect)
            return expr.as<ElementSelectExpression>().evalIndex(ctx, nullptr, unused);
        if (expr.kind == ExpressionKind::RangeSelect)
            return expr.as<RangeSelectExpression>().evalRange(ctx, nullptr);
        if (expr.kind == ExpressionKind::MemberAccess)
            return expr.as<MemberAccessExpression>().getSelectRange();
        return std::nullopt;
    };

    auto lrange = getRange(left);
    auto rrange = getRange(right);
    if (!lrange || !rrange)
        return false;

    return lrange->overlaps(*rrange);
}

bool ValueSymbol::Driver::overlaps(Compilation& compilation, const Driver& other) const {
    auto buildPath = [](const Expression* expr, SmallVector<const Expression*>& path) {
        do {
            if (expr->kind == ExpressionKind::Conversion) {
                expr = &expr->as<ConversionExpression>().operand();
            }
            else {
                path.append({ expr });
                expr = nextPrefix(*expr);
            }
        } while (expr);
    };

    SmallVectorSized<const Expression*, 4> ourPath;
    buildPath(longestStaticPrefix, ourPath);

    SmallVectorSized<const Expression*, 4> otherPath;
    buildPath(other.longestStaticPrefix, otherPath);

    EvalContext ctx(compilation);
    for (size_t i = ourPath.size(), j = otherPath.size(); i > 0 && j > 0; i--, j--) {
        auto ourElem = ourPath[i - 1];
        auto otherElem = otherPath[j - 1];
        if (!prefixOverlaps(ctx, *ourElem, *otherElem))
            return false;
    }

    return true;
}

void ValueSymbol::addDriver(DriverKind driverKind, const Expression& longestStaticPrefix) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto driver = comp.emplace<Driver>(driverKind, longestStaticPrefix);
    if (!firstDriver) {
        auto makeRef = [&]() -> const Expression& {
            BindContext bindContext(*scope, LookupLocation::min);
            SourceRange range = { location, location + name.length() };
            return ValueExpressionBase::fromSymbol(bindContext, *this, /* isHierarchical */ false,
                                                   range);
        };

        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        switch (kind) {
            case SymbolKind::Net:
                if (auto init = getInitializer())
                    firstDriver = comp.emplace<Driver>(DriverKind::Continuous, makeRef());
                break;
            case SymbolKind::Variable:
            case SymbolKind::ClassProperty:
            case SymbolKind::Field:
                if (as<VariableSymbol>().lifetime == VariableLifetime::Static) {
                    if (auto init = getInitializer())
                        firstDriver = comp.emplace<Driver>(DriverKind::Procedural, makeRef());
                }
                break;
            default:
                break;
        }

        if (!firstDriver) {
            firstDriver = driver;
            return;
        }
    }

    const bool checkOverlap =
        (VariableSymbol::isKind(kind) &&
         as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
        (kind == SymbolKind::Net && as<NetSymbol>().netType.netKind == NetType::UWire);

    // Walk the list of drivers to the end and add this one there.
    // Along the way, check that the driver is valid given the ones that already exist.
    auto curr = firstDriver;
    while (true) {
        // Variables can't be driven by multiple continuous assignments or
        // a mix of continuous and procedural assignments.
        if (checkOverlap &&
            (driverKind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) &&
            curr->overlaps(comp, *driver)) {

            auto currRange = curr->longestStaticPrefix->sourceRange;
            auto driverRange = driver->longestStaticPrefix->sourceRange;
            auto code =
                kind == SymbolKind::Net ? diag::MultipleUWireDrivers
                : (driverKind == DriverKind::Continuous && curr->kind == DriverKind::Continuous)
                    ? diag::MultipleContAssigns
                    : diag::MixedVarAssigns;

            auto& diag = scope->addDiag(code, driverRange);
            diag << name;
            diag.addNote(diag::NoteAssignedHere, currRange.start()) << currRange;
            return;
        }

        if (!curr->next) {
            curr->next = driver;
            return;
        }

        curr = curr->next;
    }
}

} // namespace slang
