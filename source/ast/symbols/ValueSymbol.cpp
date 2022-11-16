//------------------------------------------------------------------------------
// ValueSymbol.cpp
// Base class for all value symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/ValueSymbol.h"

#include <new>

#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/Scope.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

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

static bool handleOverlap(const Scope& scope, string_view name, const ValueDriver& curr,
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

        if (driver.flags.has(AssignFlags::SubFromProcedure) ||
            curr.flags.has(AssignFlags::SubFromProcedure)) {
            SourceRange extraRange = driver.flags.has(AssignFlags::SubFromProcedure)
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
        ASSERT(netType);
        diag << netType->name;
    }

    addAssignedHereNote(diag);
    return false;
}

void ValueSymbol::addDriver(DriverKind driverKind, const Expression& longestStaticPrefix,
                            const Symbol& containingSymbol, bitmask<AssignFlags> flags,
                            EvalContext* customEvalContext) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    EvalContext localEvalCtx(comp);

    auto driver = ValueDriver::create(customEvalContext ? *customEvalContext : localEvalCtx,
                                      driverKind, longestStaticPrefix, containingSymbol, flags);
    if (!driver)
        return;

    addDriverImpl(*scope, *driver);
}

void ValueSymbol::addDriver(DriverKind driverKind, const ValueDriver& copyFrom,
                            const Symbol& containingSymbol,
                            const Expression& procCallExpression) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto driver = ValueDriver::create(comp, driverKind, copyFrom, containingSymbol,
                                      procCallExpression);
    ASSERT(driver);

    addDriverImpl(*scope, *driver);
}

void ValueSymbol::addDriverImpl(const Scope& scope, const ValueDriver& driver) const {
    auto& ourType = getType();
    auto bounds = driver.getBounds(ourType);

    auto& comp = scope.getCompilation();
    if (driverMap.empty()) {
        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        auto addInitializer = [&](DriverKind driverKind) {
            auto& valExpr = *comp.emplace<NamedValueExpression>(
                *this, SourceRange{location, location + name.length()});

            EvalContext evalCtx(comp);
            auto initDriver = ValueDriver::create(evalCtx, driverKind, valExpr, scope.asSymbol(),
                                                  AssignFlags::None);
            ASSERT(initDriver);

            driverMap.insert(initDriver->getBounds(ourType), initDriver,
                             comp.getDriverMapAllocator());
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
                     (!comp.getOptions().allowDupInitialDrivers ||
                      (!curr->isInInitialBlock() && !driver.isInInitialBlock()))) {
                isProblem = true;
            }
            else if (curr->isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
                isProblem = true;
            }
        }

        if (isProblem) {
            if (!handleOverlap(scope, name, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
                               netType)) {
                break;
            }
        }
    }

    driverMap.insert(bounds, &driver, comp.getDriverMapAllocator());
}

void ValueSymbol::addPortBackref(const PortSymbol& port) const {
    auto scope = getParentScope();
    ASSERT(scope);

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
                ASSUME_UNREACHABLE;
        }
    } while (expr);
}

ValueDriver* ValueDriver::create(EvalContext& evalContext, DriverKind kind,
                                 const Expression& longestStaticPrefix,
                                 const Symbol& containingSymbol, bitmask<AssignFlags> flags) {
    SmallVector<const Expression*> path;
    visitPrefixExpressions(longestStaticPrefix,
                           [&](const Expression& expr) { path.push_back(&expr); });

    size_t allocSize = sizeof(ValueDriver) + sizeof(ConstantRange) * path.size();

    auto& comp = evalContext.compilation;
    auto mem = comp.allocate(allocSize, alignof(ValueDriver));
    auto result = new (mem)
        ValueDriver(kind, longestStaticPrefix, containingSymbol, (uint32_t)path.size(), flags);

    auto prefixMem = reinterpret_cast<ConstantRange*>(mem + sizeof(ValueDriver));

    for (size_t i = path.size(); i > 0; i--) {
        auto& elem = *path[i - 1];
        auto elemRange = elem.evalSelector(evalContext);
        if (!elemRange)
            return nullptr;

        *prefixMem = *elemRange;
        prefixMem++;
    }

    return result;
}

ValueDriver* ValueDriver::create(Compilation& comp, DriverKind kind, const ValueDriver& prefixFrom,
                                 const Symbol& containingSymbol,
                                 const Expression& procCallExpression) {
    auto prefixRanges = prefixFrom.getPrefixRanges();
    size_t allocSize = sizeof(ValueDriver) + sizeof(const Expression*) +
                       sizeof(ConstantRange) * prefixRanges.size();

    auto mem = comp.allocate(allocSize, alignof(ValueDriver));
    auto result = new (mem)
        ValueDriver(kind, *prefixFrom.prefixExpression, containingSymbol,
                    (uint32_t)prefixRanges.size(), AssignFlags::SubFromProcedure);

    auto prefixMem = reinterpret_cast<ConstantRange*>(mem + sizeof(ValueDriver));
    if (!prefixRanges.empty()) {
        memcpy(prefixMem, prefixRanges.data(), sizeof(ConstantRange) * prefixRanges.size());
        prefixMem += prefixRanges.size();
    }

    // Store the pointer to the call expression at the end of our memory range.
    *reinterpret_cast<const Expression**>(prefixMem) = &procCallExpression;

    return result;
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

span<const ConstantRange> ValueDriver::getPrefixRanges() const {
    return {reinterpret_cast<const ConstantRange*>(this + 1), numPrefixEntries};
}

SourceRange ValueDriver::getSourceRange() const {
    if (auto procCall = getProcCallExpression())
        return procCall->sourceRange;
    return prefixExpression->sourceRange;
}

const Expression* ValueDriver::getProcCallExpression() const {
    if (!flags.has(AssignFlags::SubFromProcedure))
        return nullptr;

    auto prefixMem = reinterpret_cast<const ConstantRange*>(this + 1);
    prefixMem += numPrefixEntries;
    return *reinterpret_cast<const Expression* const*>(prefixMem);
}

std::pair<uint32_t, uint32_t> ValueDriver::getBounds(const Type& rootType) const {
    auto type = &rootType.getCanonicalType();
    auto ranges = getPrefixRanges();
    auto rangeIt = ranges.begin();
    std::pair<uint32_t, uint32_t> result{0, 1};

    auto updateWidth = [&](uint32_t width) {
        // Scale the current bounds by the width of this dimension.
        // TODO: handle overflow (complicated)
        ASSERT(width);
        result.first *= width;
        result.second *= width;
    };

    auto applyRange = [&] {
        auto range = *rangeIt;
        ASSERT(range.left >= 0 && range.right >= 0);
        result.first += range.lower();
        result.second = result.first + range.width() - 1;
    };

    while (true) {
        // Figure out the bounds of this type (either the array bounds or
        // the number of elements for a struct).
        switch (type->kind) {
            case SymbolKind::FixedSizeUnpackedArrayType: {
                auto& arrayType = type->as<FixedSizeUnpackedArrayType>();
                updateWidth(arrayType.range.width());
                type = &arrayType.elementType;

                if (rangeIt != ranges.end()) {
                    applyRange();
                    rangeIt++;
                }
                break;
            }
            case SymbolKind::UnpackedStructType: {
                return result;
            }
            case SymbolKind::UnpackedUnionType: {
                // A write to any member of the union is a write to the whole thing.
                return result;
            }
            default: {
                // We don't have any more scaling to do, so apply any
                // selectors we have left and return.
                if (type->isIntegral()) {
                    updateWidth(type->getBitWidth());
                }
                else {
                    ASSERT(rangeIt == ranges.end());
                }

                for (auto end = ranges.end(); rangeIt != end; rangeIt++)
                    applyRange();
                return result;
            }
        }
    }
}

} // namespace slang::ast
