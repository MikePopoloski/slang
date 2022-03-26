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
#include "slang/symbols/BlockSymbols.h"
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

ValueSymbol::Driver::Driver(DriverKind kind, const Expression& longestStaticPrefix,
                            const ProceduralBlockSymbol* proceduralBlock,
                            bitmask<AssignFlags> flags) :
    longestStaticPrefix(&longestStaticPrefix),
    proceduralBlock(proceduralBlock), kind(kind), flags(flags) {
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

static bool handleOverlap(const Scope& scope, string_view name, const ValueSymbol::Driver& curr,
                          const ValueSymbol::Driver& driver, bool isNet, bool isUWire) {
    auto currRange = curr.longestStaticPrefix->sourceRange;
    auto driverRange = driver.longestStaticPrefix->sourceRange;

    // The default handling case for mixed vs multiple assignments is below.
    // First check for more specialized cases here:
    // 1. If this is a non-uwire net for an input or output port
    // 2. If this is a variable for an input port
    if ((isNet && (curr.isUnidirectionalPort() || driver.isUnidirectionalPort()) && !isUWire) ||
        (!isNet && (curr.isInputPort() || driver.isInputPort()))) {

        auto code = diag::InputPortAssign;
        if (isNet) {
            if (curr.flags.has(AssignFlags::InputPort))
                code = diag::InputPortCoercion;
            else
                code = diag::OutputPortCoercion;
        }

        // This is a little messy; basically we want to report the correct
        // range for the port vs the assignment. We only want to do this
        // for input ports though, as output ports show up at the instantiation
        // site and we'd rather that be considered the "port declaration".
        auto portRange = currRange;
        auto assignRange = driverRange;
        if (driver.isInputPort() || curr.flags.has(AssignFlags::OutputPort))
            std::swap(portRange, assignRange);

        auto& diag = scope.addDiag(code, assignRange);
        diag << name;

        auto note =
            code == diag::OutputPortCoercion ? diag::NoteDrivenHere : diag::NoteDeclarationHere;
        diag.addNote(note, portRange.start());

        // For variable ports this is an error, for nets it's a warning.
        return isNet;
    }

    if (curr.kind == DriverKind::Procedural && driver.kind == DriverKind::Procedural) {
        // Multiple procedural drivers where one of them is an
        // always_comb / always_ff block.
        ProceduralBlockKind procKind;
        if (driver.proceduralBlock && driver.proceduralBlock->isSingleDriverBlock()) {
            procKind = driver.proceduralBlock->procedureKind;
        }
        else {
            ASSERT(curr.proceduralBlock);
            procKind = curr.proceduralBlock->procedureKind;
            std::swap(driverRange, currRange);
        }

        string_view procName;
        switch (procKind) {
            case ProceduralBlockKind::AlwaysComb:
                procName = "always_comb"sv;
                break;
            case ProceduralBlockKind::AlwaysLatch:
                procName = "always_latch"sv;
                break;
            case ProceduralBlockKind::AlwaysFF:
                procName = "always_ff"sv;
                break;
            default:
                THROW_UNREACHABLE;
        }

        auto& diag = scope.addDiag(diag::MultipleAlwaysAssigns, driverRange);
        diag << name << procName;
        diag.addNote(diag::NoteAssignedHere, currRange.start()) << currRange;
        return false;
    }

    auto code = isUWire ? diag::MultipleUWireDrivers
                : (driver.kind == DriverKind::Continuous && curr.kind == DriverKind::Continuous)
                    ? diag::MultipleContAssigns
                    : diag::MixedVarAssigns;

    auto& diag = scope.addDiag(code, driverRange);
    diag << name;
    diag.addNote(diag::NoteAssignedHere, currRange.start()) << currRange;
    return false;
}

void ValueSymbol::addDriver(DriverKind driverKind, const Expression& longestStaticPrefix,
                            const ProceduralBlockSymbol* proceduralBlock,
                            bitmask<AssignFlags> flags) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto driver = comp.emplace<Driver>(driverKind, longestStaticPrefix, proceduralBlock, flags);

    if (!firstDriver) {
        auto makeRef = [&]() -> const Expression& {
            BindContext bindContext(*scope, LookupLocation::min, BindFlags::AllowInterconnect);
            SourceRange range = { location, location + name.length() };
            return ValueExpressionBase::fromSymbol(bindContext, *this, /* isHierarchical */ false,
                                                   range);
        };

        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        switch (kind) {
            case SymbolKind::Net:
                if (getInitializer()) {
                    firstDriver = comp.emplace<Driver>(DriverKind::Continuous, makeRef(), nullptr,
                                                       AssignFlags::None);
                }
                break;
            case SymbolKind::Variable:
            case SymbolKind::ClassProperty:
            case SymbolKind::Field:
                if (as<VariableSymbol>().lifetime == VariableLifetime::Static && getInitializer()) {
                    firstDriver = comp.emplace<Driver>(DriverKind::Procedural, makeRef(), nullptr,
                                                       AssignFlags::None);
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

    // We need to check for overlap in the following cases:
    // - static variables (automatic variables can't ever be driven continuously)
    // - uwire nets
    const bool isNet = kind == SymbolKind::Net;
    const bool isUWire = isNet && as<NetSymbol>().netType.netKind == NetType::UWire;
    const bool checkOverlap = (VariableSymbol::isKind(kind) &&
                               as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
                              isUWire;

    // Walk the list of drivers to the end and add this one there.
    // Along the way, check that the driver is valid given the ones that already exist.
    auto curr = firstDriver;
    while (true) {
        // Determine whether we should check this pair of drivers for overlap.
        // - If this is for a mix of input/output and inout ports, always check.
        // - Don't check for "Other" drivers (procedural force / release, etc)
        // - Otherwise, if is this a static var or uwire net:
        //      - Check if a mix of continuous and procedural assignments
        //      - Check if multiple continuous assignments
        //      - If both procedural, check that there aren't multiple
        //        always_comb / always_ff procedures.
        bool shouldCheck = false;
        if (curr->isUnidirectionalPort() != driver->isUnidirectionalPort()) {
            shouldCheck = true;
        }
        else if (checkOverlap && driverKind != DriverKind::Other &&
                 curr->kind != DriverKind::Other) {
            if (driverKind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) {
                shouldCheck = true;
            }
            else if (curr->proceduralBlock != proceduralBlock &&
                     ((curr->proceduralBlock && curr->proceduralBlock->isSingleDriverBlock()) ||
                      (proceduralBlock && proceduralBlock->isSingleDriverBlock()))) {
                shouldCheck = true;
            }
        }

        if (shouldCheck && curr->overlaps(comp, *driver)) {
            if (!handleOverlap(*scope, name, *curr, *driver, isNet, isUWire))
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
