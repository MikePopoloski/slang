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
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/ExpressionsDiags.h"
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

static bool handleOverlap(const Scope& scope, std::string_view name, const ValueDriver& curr,
                          const ValueDriver& driver, bool isNet, bool isUWire,
                          bool isSingleDriverUDNT, const NetType* netType) {
    auto currRange = curr.getSourceRange();
    auto driverRange = driver.getSourceRange();

    // The default handling case for mixed vs multiple assignments is below.
    // First check for more specialized cases here:
    // 1. If this is a non-uwire net for an input or output port
    // 2. If this is a variable for an input port
    const bool isUnidirectionNetPort = isNet && (curr.isUnidirectionalPort() ||
                                                 driver.isUnidirectionalPort());

    if ((isUnidirectionNetPort && !isUWire && !isSingleDriverUDNT) ||
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

        auto note = code == diag::OutputPortCoercion ? diag::NoteDrivenHere
                                                     : diag::NoteDeclarationHere;
        diag.addNote(note, portRange);

        // For variable ports this is an error, for nets it's a warning.
        return isNet;
    }

    if (curr.isClockVar() || driver.isClockVar()) {
        // Both drivers being clockvars is allowed.
        if (curr.isClockVar() && driver.isClockVar())
            return true;

        // Procedural drivers are allowed to clockvars.
        if (curr.kind == DriverKind::Procedural || driver.kind == DriverKind::Procedural)
            return true;

        // Otherwise we have an error.
        if (driver.isClockVar())
            std::swap(driverRange, currRange);

        auto& diag = scope.addDiag(diag::ClockVarTargetAssign, driverRange);
        diag << name;
        diag.addNote(diag::NoteReferencedHere, currRange);
        return false;
    }

    if (curr.isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
        auto& diag = scope.addDiag(diag::LocalFormalVarMultiAssign, driverRange);
        diag << name;
        diag.addNote(diag::NoteAssignedHere, currRange);
        return false;
    }

    auto addAssignedHereNote = [&](Diagnostic& d) {
        // If the two locations are the same, the symbol is driven by
        // the same source location but two different parts of the hierarchy.
        // In those cases we want a different note about what's going on.
        if (currRange.start() != driverRange.start()) {
            d.addNote(diag::NoteAssignedHere, currRange);
        }
        else {
            auto& note = d.addNote(diag::NoteFromHere2, SourceLocation::NoLocation);

            std::string buf;
            driver.containingSymbol->getHierarchicalPath(buf);
            note << buf;

            buf.clear();
            curr.containingSymbol->getHierarchicalPath(buf);
            note << buf;
        }
    };

    if (curr.kind == DriverKind::Procedural && driver.kind == DriverKind::Procedural) {
        // Multiple procedural drivers where one of them is an
        // always_comb / always_ff block.
        ProceduralBlockKind procKind;
        if (driver.isInSingleDriverProcedure()) {
            procKind = driver.containingSymbol->as<ProceduralBlockSymbol>().procedureKind;
        }
        else {
            procKind = curr.containingSymbol->as<ProceduralBlockSymbol>().procedureKind;
            std::swap(driverRange, currRange);
        }

        auto& diag = scope.addDiag(diag::MultipleAlwaysAssigns, driverRange);
        diag << name << SemanticFacts::getProcedureKindStr(procKind);
        addAssignedHereNote(diag);

        if (driver.procCallExpression || curr.procCallExpression) {
            SourceRange extraRange = driver.procCallExpression
                                         ? driver.prefixExpression->sourceRange
                                         : curr.prefixExpression->sourceRange;

            diag.addNote(diag::NoteOriginalAssign, extraRange);
        }

        return false;
    }

    DiagCode code;
    if (isUWire)
        code = diag::MultipleUWireDrivers;
    else if (isSingleDriverUDNT)
        code = diag::MultipleUDNTDrivers;
    else if (driver.kind == DriverKind::Continuous && curr.kind == DriverKind::Continuous)
        code = diag::MultipleContAssigns;
    else
        code = diag::MixedVarAssigns;

    auto& diag = scope.addDiag(code, driverRange);
    diag << name;
    if (isSingleDriverUDNT) {
        SLANG_ASSERT(netType);
        diag << netType->name;
    }

    addAssignedHereNote(diag);
    return false;
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

    auto driver = comp.emplace<ValueDriver>(driverKind, longestStaticPrefix, containingSymbol,
                                            flags);
    addDriver(*bounds, *driver);
}

void ValueSymbol::addDriver(DriverKind driverKind, DriverBitRange bounds,
                            const Expression& longestStaticPrefix, const Symbol& containingSymbol,
                            const Expression& procCallExpression) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto driver = comp.emplace<ValueDriver>(driverKind, longestStaticPrefix, containingSymbol,
                                            AssignFlags::None);
    driver->procCallExpression = &procCallExpression;

    addDriver(bounds, *driver);
}

void ValueSymbol::addDriver(DriverBitRange bounds, const ValueDriver& driver) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();

    if (driverMap.empty()) {
        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        auto addInitializer = [&](DriverKind driverKind) {
            auto& valExpr = *comp.emplace<NamedValueExpression>(
                *this, SourceRange{location, location + name.length()});

            DriverBitRange initBounds{0, getType().getSelectableWidth() - 1};
            auto initDriver = comp.emplace<ValueDriver>(driverKind, valExpr, scope->asSymbol(),
                                                        AssignFlags::None);

            driverMap.insert(initBounds, initDriver, comp.getDriverMapAllocator());
        };

        switch (kind) {
            case SymbolKind::Net:
                if (getInitializer())
                    addInitializer(DriverKind::Continuous);
                break;
            case SymbolKind::Variable:
            case SymbolKind::ClassProperty:
            case SymbolKind::Field:
                if (getInitializer())
                    addInitializer(DriverKind::Procedural);
                break;
            default:
                break;
        }

        if (driverMap.empty()) {
            driverMap.insert(bounds, &driver, comp.getDriverMapAllocator());
            return;
        }
    }

    // We need to check for overlap in the following cases:
    // - static variables (automatic variables can't ever be driven continuously)
    // - uwire nets
    // - user-defined nets with no resolution function
    const bool isNet = kind == SymbolKind::Net;
    bool isUWire = false;
    bool isSingleDriverUDNT = false;
    const NetType* netType = nullptr;

    if (isNet) {
        netType = &as<NetSymbol>().netType;
        isUWire = netType->netKind == NetType::UWire;
        isSingleDriverUDNT = netType->netKind == NetType::UserDefined &&
                             netType->getResolutionFunction() == nullptr;
    }

    const bool checkOverlap = (VariableSymbol::isKind(kind) &&
                               as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
                              isUWire || isSingleDriverUDNT ||
                              kind == SymbolKind::LocalAssertionVar;

    // TODO: try to clean these conditions up a bit more
    auto end = driverMap.end();
    for (auto it = driverMap.find(bounds); it != end; ++it) {
        // Check whether this pair of drivers overlapping constitutes a problem.
        // The conditions for reporting a problem are:
        // - If this is for a mix of input/output and inout ports, always report.
        // - Don't report for "Other" drivers (procedural force / release, etc)
        // - Otherwise, if is this a static var or uwire net:
        //      - Report if a mix of continuous and procedural assignments
        //      - Don't report if both drivers are sliced ports from an array
        //        of instances. We already sliced these up correctly when the
        //        connections were made and the overlap logic here won't work correctly.
        //      - Report if multiple continuous assignments
        //      - If both procedural, report if there aren multiple
        //        always_comb / always_ff procedures.
        //          - If the allowDupInitialDrivers option is set, allow an initial
        //            block to overlap even if the other block is an always_comb/ff.
        // - Assertion local variable formal arguments can't drive more than
        //   one output to the same local variable.
        bool isProblem = false;
        auto curr = *it;

        if (curr->isUnidirectionalPort() != driver.isUnidirectionalPort()) {
            isProblem = true;
        }
        else if (checkOverlap && driver.kind != DriverKind::Other &&
                 curr->kind != DriverKind::Other) {
            if (driver.kind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) {
                if (!driver.flags.has(AssignFlags::SlicedPort) ||
                    !curr->flags.has(AssignFlags::SlicedPort)) {
                    isProblem = true;
                }
            }
            else if (curr->containingSymbol != driver.containingSymbol &&
                     curr->containingSymbol->kind == SymbolKind::ProceduralBlock &&
                     driver.containingSymbol->kind == SymbolKind::ProceduralBlock &&
                     (curr->isInSingleDriverProcedure() || driver.isInSingleDriverProcedure()) &&
                     (!comp.hasFlag(CompilationFlags::AllowDupInitialDrivers) ||
                      (!curr->isInInitialBlock() && !driver.isInInitialBlock()))) {
                isProblem = true;
            }
            else if (curr->isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
                isProblem = true;
            }
        }

        if (isProblem) {
            if (!handleOverlap(*scope, name, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
                               netType)) {
                break;
            }
        }
    }

    driverMap.insert(bounds, &driver, comp.getDriverMapAllocator());
}

void ValueSymbol::addPortBackref(const PortSymbol& port) const {
    auto scope = getParentScope();
    SLANG_ASSERT(scope);

    auto& comp = scope->getCompilation();
    firstPortBackref = comp.emplace<PortBackref>(port, firstPortBackref);
}

template<typename TCallback>
static void visitPrefixExpressions(const Expression& longestStaticPrefix, TCallback&& callback) {
    auto expr = &longestStaticPrefix;
    do {
        switch (expr->kind) {
            case ExpressionKind::NamedValue:
            case ExpressionKind::HierarchicalValue:
            case ExpressionKind::Call:
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

bool ValueDriver::isInSingleDriverProcedure() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().isSingleDriverBlock();
}

bool ValueDriver::isInSubroutine() const {
    return containingSymbol->kind == SymbolKind::Subroutine;
}

bool ValueDriver::isInInitialBlock() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().procedureKind ==
               ProceduralBlockKind::Initial;
}

bool ValueDriver::isInAlwaysFFBlock() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().procedureKind ==
               ProceduralBlockKind::AlwaysFF;
}

bool ValueDriver::isInAlwaysLatchBlock() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().procedureKind ==
               ProceduralBlockKind::AlwaysLatch;
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
    visitPrefixExpressions(prefixExpression,
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
