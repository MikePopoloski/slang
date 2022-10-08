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

ValueSymbol::Driver& ValueSymbol::Driver::create(EvalContext& evalContext, DriverKind kind,
                                                 const Expression& longestStaticPrefix,
                                                 const Symbol& containingSymbol,
                                                 bitmask<AssignFlags> flags, SourceRange range) {
    SmallVector<const Expression*> path;
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
                path.push_back({expr});
                expr = &expr->as<ElementSelectExpression>().value();
                break;
            case ExpressionKind::RangeSelect:
                path.push_back({expr});
                expr = &expr->as<RangeSelectExpression>().value();
                break;
            case ExpressionKind::MemberAccess:
                path.push_back({expr});
                expr = &expr->as<MemberAccessExpression>().value();
                break;
            default:
                ASSUME_UNREACHABLE;
        }
    } while (expr);

    bool hasOriginalRange = range.start() && range.end();
    size_t allocSize = sizeof(Driver) + sizeof(ConstantRange) * path.size();
    if (hasOriginalRange)
        allocSize += sizeof(SourceRange);

    auto& comp = evalContext.compilation;
    auto mem = comp.allocate(allocSize, alignof(Driver));
    auto result = new (mem)
        Driver(kind, containingSymbol, flags, (uint32_t)path.size(), hasOriginalRange);
    result->sourceRange = longestStaticPrefix.sourceRange;

    auto prefixMem = reinterpret_cast<ConstantRange*>(mem + sizeof(Driver));

    for (size_t i = path.size(); i > 0; i--) {
        auto& elem = *path[i - 1];
        auto elemRange = elem.evalSelector(evalContext);
        if (!elemRange)
            result->hasError = true;
        else
            *prefixMem = *elemRange;
        prefixMem++;
    }

    if (hasOriginalRange) {
        result->sourceRange = range;
        *reinterpret_cast<SourceRange*>(prefixMem) = longestStaticPrefix.sourceRange;
    }

    return *result;
}

ValueSymbol::Driver& ValueSymbol::Driver::create(Compilation& comp, DriverKind kind,
                                                 span<const ConstantRange> longestStaticPrefix,
                                                 const Symbol& containingSymbol,
                                                 bitmask<AssignFlags> flags, SourceRange range,
                                                 SourceRange originalRange) {
    bool hasOriginalRange = originalRange.start() && originalRange.end();
    size_t allocSize = sizeof(Driver) + sizeof(ConstantRange) * longestStaticPrefix.size();
    if (hasOriginalRange)
        allocSize += sizeof(SourceRange);

    auto mem = comp.allocate(allocSize, alignof(Driver));
    auto result = new (mem) Driver(kind, containingSymbol, flags,
                                   (uint32_t)longestStaticPrefix.size(), hasOriginalRange);
    result->sourceRange = range;

    auto prefixMem = reinterpret_cast<ConstantRange*>(mem + sizeof(Driver));
    if (!longestStaticPrefix.empty()) {
        memcpy(prefixMem, longestStaticPrefix.data(),
               sizeof(ConstantRange) * longestStaticPrefix.size());

        prefixMem += longestStaticPrefix.size();
    }

    if (hasOriginalRange)
        *reinterpret_cast<SourceRange*>(prefixMem) = originalRange;

    return *result;
}

bool ValueSymbol::Driver::isInSingleDriverProcedure() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().isSingleDriverBlock();
}

bool ValueSymbol::Driver::isInSubroutine() const {
    return containingSymbol->kind == SymbolKind::Subroutine;
}

bool ValueSymbol::Driver::isInInitialBlock() const {
    return containingSymbol->kind == SymbolKind::ProceduralBlock &&
           containingSymbol->as<ProceduralBlockSymbol>().procedureKind ==
               ProceduralBlockKind::Initial;
}

span<const ConstantRange> ValueSymbol::Driver::getPrefix() const {
    return {reinterpret_cast<const ConstantRange*>(this + 1), numPrefixEntries};
}

SourceRange ValueSymbol::Driver::getOriginalRange() const {
    ASSERT(hasOriginalRange);

    auto mem = reinterpret_cast<const ConstantRange*>(this + 1);
    mem += numPrefixEntries;
    return *reinterpret_cast<const SourceRange*>(mem);
}

bool ValueSymbol::Driver::overlaps(const Driver& other) const {
    if (hasError || other.hasError)
        return false;

    auto ourPath = getPrefix();
    auto otherPath = other.getPrefix();

    for (size_t i = 0, j = 0; i < ourPath.size() && j < otherPath.size(); i++, j++) {
        auto ourElem = ourPath[i];
        auto otherElem = otherPath[j];
        if (!ourElem.overlaps(otherElem))
            return false;
    }

    return true;
}

static bool handleOverlap(const Scope& scope, string_view name, const ValueSymbol::Driver& curr,
                          const ValueSymbol::Driver& driver, bool isNet, bool isUWire,
                          bool isSingleDriverUDNT, const NetType* netType) {
    auto currRange = curr.sourceRange;
    auto driverRange = driver.sourceRange;

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
                                         ? driver.getOriginalRange()
                                         : curr.getOriginalRange();

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
                            SourceRange rangeOverride, EvalContext* customEvalContext) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    EvalContext localEvalCtx(comp);
    EvalContext* evalCtxPtr = customEvalContext;
    if (!evalCtxPtr)
        evalCtxPtr = &localEvalCtx;

    auto& driver = Driver::create(*evalCtxPtr, driverKind, longestStaticPrefix, containingSymbol,
                                  flags, rangeOverride);
    addDriverImpl(*scope, driver);
}

void ValueSymbol::addDriver(DriverKind driverKind, const Driver& copyFrom,
                            const Symbol& containingSymbol, bitmask<AssignFlags> flags,
                            SourceRange rangeOverride) const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& comp = scope->getCompilation();
    auto& driver = Driver::create(comp, driverKind, copyFrom.getPrefix(), containingSymbol, flags,
                                  rangeOverride, copyFrom.sourceRange);
    addDriverImpl(*scope, driver);
}

void ValueSymbol::addDriverImpl(const Scope& scope, const Driver& driver) const {
    auto& comp = scope.getCompilation();
    if (!firstDriver) {
        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        auto create = [&](DriverKind driverKind) {
            return &Driver::create(comp, driverKind, {}, scope.asSymbol(), AssignFlags::None,
                                   {location, location + name.length()}, {});
        };

        switch (kind) {
            case SymbolKind::Net:
                if (getInitializer())
                    firstDriver = create(DriverKind::Continuous);
                break;
            case SymbolKind::Variable:
            case SymbolKind::ClassProperty:
            case SymbolKind::Field:
                if (getInitializer())
                    firstDriver = create(DriverKind::Procedural);
                break;
            default:
                break;
        }

        if (!firstDriver) {
            firstDriver = &driver;
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

    // Walk the list of drivers to the end and add this one there.
    // Along the way, check that the driver is valid given the ones that already exist.
    auto curr = firstDriver;
    while (true) {
        // Determine whether we should check this pair of drivers for overlap.
        // - If this is for a mix of input/output and inout ports, always check.
        // - Don't check for "Other" drivers (procedural force / release, etc)
        // - Otherwise, if is this a static var or uwire net:
        //      - Check if a mix of continuous and procedural assignments
        //      - Don't check if both drivers are sliced ports from an array
        //        of instances. We already sliced these up correctly when the
        //        connections were made and the overlap logic here won't work correctly.
        //      - Check if multiple continuous assignments
        //      - If both procedural, check that there aren't multiple
        //        always_comb / always_ff procedures.
        //          - If the allowDupInitialDrivers option is set, allow an initial
        //            block to overlap even if the other block is an always_comb/ff.
        // - Assertion local variable formal arguments can't drive more than
        //   one output to the same local variable.
        bool shouldCheck = false;
        if (curr->isUnidirectionalPort() != driver.isUnidirectionalPort()) {
            shouldCheck = true;
        }
        else if (checkOverlap && driver.kind != DriverKind::Other &&
                 curr->kind != DriverKind::Other) {
            if (driver.kind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) {
                if (!driver.flags.has(AssignFlags::SlicedPort) ||
                    !curr->flags.has(AssignFlags::SlicedPort)) {
                    shouldCheck = true;
                }
            }
            else if (curr->containingSymbol != driver.containingSymbol &&
                     curr->containingSymbol->kind == SymbolKind::ProceduralBlock &&
                     driver.containingSymbol->kind == SymbolKind::ProceduralBlock &&
                     (curr->isInSingleDriverProcedure() || driver.isInSingleDriverProcedure()) &&
                     (!comp.getOptions().allowDupInitialDrivers ||
                      (!curr->isInInitialBlock() && !driver.isInInitialBlock()))) {

                shouldCheck = true;
            }
            else if (curr->isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
                shouldCheck = true;
            }
        }

        if (shouldCheck && curr->overlaps(driver)) {
            if (!handleOverlap(scope, name, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
                               netType)) {
                return;
            }
        }

        if (!curr->next) {
            curr->next = &driver;
            return;
        }

        curr = curr->next;
    }
}

} // namespace slang::ast
