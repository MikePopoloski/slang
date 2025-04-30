//------------------------------------------------------------------------------
// AnalysisScopeVisitor.h
// Internal visitor for analyzing a scope
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "NonProceduralExprVisitor.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/util/TypeTraits.h"

namespace slang::analysis {

using namespace ast;

static bool hasUnusedAttrib(const Compilation& compilation, const Symbol& symbol) {
    for (auto attr : compilation.getAttributes(symbol)) {
        if (attr->name == "unused"sv || attr->name == "maybe_unused"sv)
            return attr->getValue().isTrue();
    }
    return false;
}

struct AnalysisScopeVisitor {
    AnalysisManager::WorkerState& state;
    AnalysisContext& context;
    AnalysisManager& manager;
    AnalyzedScope& result;
    const AnalyzedProcedure* parentProcedure;

    AnalysisScopeVisitor(AnalysisManager::WorkerState& state, AnalyzedScope& scope,
                         const AnalyzedProcedure* parentProcedure) :
        state(state), context(state.context), manager(*context.manager), result(scope),
        parentProcedure(parentProcedure) {}

    void visit(const InstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
        visitExprs(symbol);
    }

    void visit(const CheckerInstanceSymbol& symbol) {
        // Ignore procedural checkers here; they will be handled by their parent procedure.
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated) || symbol.body.isProcedural)
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
        visitExprs(symbol);
    }

    void visit(const PackageSymbol& symbol) {
        // Kick off an async analysis of the package.
        // Our caller up the chain (we must be in a compilation unit here)
        // will take care of looking these up and hooking them into the
        // final AnalyzedDesign that we return.
        manager.analyzeScopeAsync(symbol);
    }

    void visit(const GenerateBlockSymbol& symbol) {
        if (symbol.isUninstantiated)
            return;

        // For our purposes we can just flatten the content of generate
        // blocks into their parents.
        visitMembers(symbol);
    }

    void visit(const GenerateBlockArraySymbol& symbol) {
        if (!symbol.valid)
            return;

        visitMembers(symbol);
    }

    void visit(const ProceduralBlockSymbol& symbol) {
        result.procedures.emplace_back(context, symbol, parentProcedure);

        for (auto& [valueSym, drivers] : result.procedures.back().getDrivers()) {
            auto updateFunc = [&](auto& elem) {
                for (auto& [driver, bounds] : drivers)
                    addDriver(*elem.first, elem.second, *driver, bounds);
            };
            manager.symbolDrivers.try_emplace_and_visit(valueSym, updateFunc, updateFunc);
        }
    }

    void visit(const SubroutineSymbol& symbol) {
        if (symbol.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize |
                             MethodFlags::BuiltIn)) {
            return;
        }

        result.procedures.emplace_back(context, symbol);
        visitMembers(symbol);
    }

    void visit(const MethodPrototypeSymbol&) {
        // Deliberately don't visit the method prototype's formal arguments.
    }

    void visit(const ClassType& symbol) {
        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const CovergroupType& symbol) {
        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
        visitExprs(symbol);
    }

    void visit(const GenericClassDefSymbol& symbol) {
        for (auto& spec : symbol.specializations())
            spec.visit(*this);
    }

    void visit(const NetSymbol& symbol) {
        visitExprs(symbol);

        if (symbol.isImplicit) {
            checkValueUnused(symbol, diag::UnusedImplicitNet, diag::UnusedImplicitNet,
                             diag::UnusedImplicitNet);
        }
        else {
            checkValueUnused(symbol, diag::UnusedNet, diag::UndrivenNet, diag::UnusedButSetNet);
        }
    }

    void visit(const VariableSymbol& symbol) {
        visitExprs(symbol);

        if (symbol.flags.has(VariableFlags::CompilerGenerated))
            return;

        if (symbol.kind == SymbolKind::Variable) {
            // Class handles and covergroups are considered used if they are
            // constructed, since construction can have side effects.
            auto& type = symbol.getType();
            if (type.isClass() || type.isCovergroup()) {
                if (auto init = symbol.getDeclaredType()->getInitializer();
                    init && (init->kind == ExpressionKind::NewClass ||
                             init->kind == ExpressionKind::NewCovergroup)) {
                    return;
                }
            }

            checkValueUnused(symbol, diag::UnusedVariable, diag::UnassignedVariable,
                             diag::UnusedButSetVariable);
        }
        else if (symbol.kind == SymbolKind::FormalArgument) {
            auto parent = symbol.getParentScope();
            SLANG_ASSERT(parent);

            if (parent->asSymbol().kind == SymbolKind::Subroutine) {
                auto& sub = parent->asSymbol().as<SubroutineSymbol>();
                if (!sub.isVirtual())
                    checkValueUnused(symbol, diag::UnusedArgument, std::nullopt, std::nullopt);
            }
        }
    }

    void visit(const ParameterSymbol& symbol) {
        checkValueUnused(symbol, diag::UnusedParameter, {}, diag::UnusedParameter);
    }

    void visit(const TypeParameterSymbol& symbol) {
        checkUnused(symbol, diag::UnusedTypeParameter);
    }

    void visit(const TypeAliasType& symbol) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        {
            auto [used, _] = isReferenced(*syntax);
            if (used)
                return;
        }

        // If this is a typedef for an enum declaration, count usage
        // of any of the enum values as a usage of the typedef itself
        // (since there's no good way otherwise to introduce enum values
        // without the typedef).
        auto& targetType = symbol.targetType.getType();
        if (targetType.kind == SymbolKind::EnumType) {
            for (auto& val : targetType.as<EnumType>().values()) {
                if (auto valSyntax = val.getSyntax()) {
                    auto [valUsed, _] = isReferenced(*valSyntax);
                    if (valUsed)
                        return;
                }
            }
        }

        addDiag(symbol, diag::UnusedTypedef);
    }

    void visit(const GenvarSymbol& symbol) { checkUnused(symbol, diag::UnusedGenvar); }

    void visit(const SequenceSymbol& symbol) { checkAssertionDeclUnused(symbol, "sequence"sv); }
    void visit(const PropertySymbol& symbol) { checkAssertionDeclUnused(symbol, "property"sv); }
    void visit(const LetDeclSymbol& symbol) { checkAssertionDeclUnused(symbol, "let"sv); }
    void visit(const CheckerSymbol& symbol) { checkAssertionDeclUnused(symbol, "checker"sv); }

    void visit(const ExplicitImportSymbol& symbol) { checkUnused(symbol, diag::UnusedImport); }

    void visit(const WildcardImportSymbol& symbol) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax)
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used) {
            if (shouldWarn(symbol))
                context.addDiag(symbol, diag::UnusedWildcardImport, symbol.location);
        }
    }

    template<typename T>
        requires(IsAnyOf<T, InstanceArraySymbol, ClockingBlockSymbol, AnonymousProgramSymbol,
                         SpecifyBlockSymbol, CovergroupBodySymbol, CoverCrossSymbol,
                         CoverCrossBodySymbol, StatementBlockSymbol, RandSeqProductionSymbol>)
    void visit(const T& symbol) {
        visitExprs(symbol);

        // For these symbol types we just descend into their members
        // and flatten them into their parent scope.
        visitMembers(symbol);
    }

    // Everything else doesn't need to be analyzed (except visiting expressions, if necessary).
    template<typename T>
        requires(
            IsAnyOf<T, InvalidSymbol, RootSymbol, CompilationUnitSymbol, DefinitionSymbol,
                    AttributeSymbol, TransparentMemberSymbol, EmptyMemberSymbol, EnumValueSymbol,
                    ForwardingTypedefSymbol, PortSymbol, MultiPortSymbol, InterfacePortSymbol,
                    InstanceBodySymbol, ModportSymbol, ModportPortSymbol, ModportClockingSymbol,
                    ContinuousAssignSymbol, ElabSystemTaskSymbol, UninstantiatedDefSymbol,
                    ConstraintBlockSymbol, DefParamSymbol, SpecparamSymbol, PrimitiveSymbol,
                    PrimitivePortSymbol, PrimitiveInstanceSymbol, AssertionPortSymbol,
                    CoverpointSymbol, CoverageBinSymbol, TimingPathSymbol, PulseStyleSymbol,
                    SystemTimingCheckSymbol, NetAliasSymbol, ConfigBlockSymbol, NetType,
                    CheckerInstanceBodySymbol> ||
            std::is_base_of_v<Type, T>)
    void visit(const T& symbol) {
        visitExprs(symbol);
    }

private:
    template<typename T>
    void visitMembers(const T& symbol) {
        for (auto& member : symbol.members())
            member.visit(*this);
    }

    template<typename T>
    void visitExprs(const T& symbol) {
        if constexpr (HasVisitExprs<T, NonProceduralExprVisitor>) {
            NonProceduralExprVisitor visitor(context, symbol);
            symbol.visitExprs(visitor);
        }
    }

    void checkValueUnused(const ValueSymbol& symbol, DiagCode unusedCode,
                          std::optional<DiagCode> unsetCode, std::optional<DiagCode> unreadCode) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [rvalue, lvalue] = isReferenced(*syntax);

        auto portRef = symbol.getFirstPortBackref();
        if (portRef) {
            // This is a variable or net connected internally to a port.
            // If there is more than one port connection something unusually
            // complicated is going on so don't try to diagnose warnings.
            if (portRef->getNextBackreference())
                return;

            // Otherwise check and warn about the port being unused.
            switch (portRef->port->direction) {
                case ArgumentDirection::In:
                    if (!rvalue)
                        addDiag(symbol, diag::UnusedPort);
                    break;
                case ArgumentDirection::Out:
                    if (!lvalue)
                        addDiag(symbol, diag::UndrivenPort);
                    break;
                case ArgumentDirection::InOut:
                    if (!rvalue && !lvalue)
                        addDiag(symbol, diag::UnusedPort);
                    else if (!rvalue)
                        addDiag(symbol, diag::UnusedButSetPort);
                    else if (!lvalue)
                        addDiag(symbol, diag::UndrivenPort);
                    break;
                case ArgumentDirection::Ref:
                    if (!rvalue && !lvalue)
                        addDiag(symbol, diag::UnusedPort);
                    break;
            }
            return;
        }

        if (!rvalue && !lvalue)
            addDiag(symbol, unusedCode);
        else if (!rvalue && unreadCode)
            addDiag(symbol, *unreadCode);
        else if (!lvalue && !symbol.getDeclaredType()->getInitializerSyntax() && unsetCode)
            addDiag(symbol, *unsetCode);
    }

    void checkUnused(const Symbol& symbol, DiagCode code) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used)
            addDiag(symbol, code);
    }

    void checkAssertionDeclUnused(const Symbol& symbol, std::string_view kind) {
        if (!manager.hasFlag(AnalysisFlags::CheckUnused))
            return;

        auto syntax = symbol.getSyntax();
        if (!syntax || symbol.name.empty())
            return;

        auto [used, _] = isReferenced(*syntax);
        if (!used && shouldWarn(symbol)) {
            context.addDiag(symbol, diag::UnusedAssertionDecl, symbol.location)
                << kind << symbol.name;
        }
    }

    bool shouldWarn(const Symbol& symbol) {
        auto scope = symbol.getParentScope();
        return !scope->isUninstantiated() && scope->asSymbol().kind != SymbolKind::Package &&
               symbol.name != "_"sv && !hasUnusedAttrib(scope->getCompilation(), symbol);
    }

    void addDiag(const Symbol& symbol, DiagCode code) {
        if (shouldWarn(symbol))
            context.addDiag(symbol, code, symbol.location) << symbol.name;
    }

    std::pair<bool, bool> isReferenced(const syntax::SyntaxNode& node) const {
        return result.scope.getCompilation().isReferenced(node);
    }

    void addDriver(const ValueSymbol& symbol, AnalysisManager::SymbolDriverMap& driverMap,
                   const ValueDriver& driver, DriverBitRange bounds) {
        auto scope = symbol.getParentScope();
        SLANG_ASSERT(scope);

        // If this driver is made via an interface port connection we want to
        // note that fact as it represents a side effect for the instance that
        // is not captured in the port connections.
        // bool isIfacePortDriver = false;
        // if (!driver.isFromSideEffect) {
        //     visitPrefixExpressions(*driver.prefixExpression, /* includeRoot */ true,
        //                            [&](const Expression& expr) {
        //                                if (expr.kind == ExpressionKind::HierarchicalValue) {
        //                                    auto& hve = expr.as<HierarchicalValueExpression>();
        //                                    if (hve.ref.isViaIfacePort()) {
        //                                        isIfacePortDriver = true;
        //                                        comp.noteInterfacePortDriver(hve.ref, driver);
        //                                    }
        //                                }
        //                            });
        // }

        if (driverMap.empty()) {
            // The first time we add a driver, check whether there is also an
            // initializer expression that should count as a driver as well.
            auto addInitializer = [&](DriverKind driverKind) {
                auto& valExpr = *context.alloc.emplace<NamedValueExpression>(
                    symbol, SourceRange{symbol.location, symbol.location + symbol.name.length()});

                DriverBitRange initBounds{0, symbol.getType().getSelectableWidth() - 1};
                auto initDriver = context.alloc.emplace<ValueDriver>(driverKind, valExpr,
                                                                     scope->asSymbol(),
                                                                     AssignFlags::None);

                driverMap.insert(initBounds, initDriver, state.driverAlloc);
            };

            switch (symbol.kind) {
                case SymbolKind::Net:
                    if (symbol.getInitializer())
                        addInitializer(DriverKind::Continuous);
                    break;
                case SymbolKind::Variable:
                case SymbolKind::ClassProperty:
                case SymbolKind::Field:
                    if (symbol.getInitializer())
                        addInitializer(DriverKind::Procedural);
                    break;
                default:
                    break;
            }

            if (driverMap.empty()) {
                driverMap.insert(bounds, &driver, state.driverAlloc);
                return;
            }
        }

        // We need to check for overlap in the following cases:
        // - static variables (automatic variables can't ever be driven continuously)
        // - uwire nets
        // - user-defined nets with no resolution function
        const bool isNet = symbol.kind == SymbolKind::Net;
        bool isUWire = false;
        bool isSingleDriverUDNT = false;
        const NetType* netType = nullptr;

        if (isNet) {
            netType = &symbol.as<NetSymbol>().netType;
            isUWire = netType->netKind == NetType::UWire;
            isSingleDriverUDNT = netType->netKind == NetType::UserDefined &&
                                 netType->getResolutionFunction() == nullptr;
        }

        const bool checkOverlap =
            (VariableSymbol::isKind(symbol.kind) &&
             symbol.as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
            isUWire || isSingleDriverUDNT || symbol.kind == SymbolKind::LocalAssertionVar;

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
                         curr->isInProcedure() && driver.isInProcedure() &&
                         (curr->isInSingleDriverProcedure() || driver.isInSingleDriverProcedure())
                         // TODO:
                         //   &&
                         //  (!comp.hasFlag(CompilationFlags::AllowDupInitialDrivers) ||
                         //   (curr->source != DriverSource::Initial &&
                         //    driver.source != DriverSource::Initial))
                ) {
                    isProblem = true;
                }
                else if (curr->isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
                    isProblem = true;
                }
            }

            if (isProblem) {
                // One last annoying special case: if the previous driver was applied as a
                // side effect of skipping an instance due to it being cached, and then later
                // we found we had to visit that instance due to a downward name into it,
                // we might now be trying to reapply the same driver that caused the original
                // side effect, which would cause spurious multi-driven errors. Detect that
                // case and skip it here.
                // if (isIfacePortDriver && curr->isFromSideEffect) [[unlikely]] {
                //     if (isContainedWithin(*driver.containingSymbol, *curr->containingSymbol))
                //         continue;
                // }
                // else if (driver.isFromSideEffect &&
                //          isContainedWithin(*curr->containingSymbol, *driver.containingSymbol)) {
                //     // This operates in reverse as well; someone already visited the instance
                //     // manually and now we're trying to apply a side effect that has already
                //     // been applied.
                //     continue;
                // }

                if (!handleOverlap(symbol, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
                                   netType)) {
                    break;
                }
            }
        }

        driverMap.insert(bounds, &driver, state.driverAlloc);
    }

    bool handleOverlap(const ValueSymbol& symbol, const ValueDriver& curr,
                       const ValueDriver& driver, bool isNet, bool isUWire, bool isSingleDriverUDNT,
                       const NetType* netType) {
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

            auto& diag = context.addDiag(symbol, code, assignRange);
            diag << symbol.name;

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

            auto& diag = context.addDiag(symbol, diag::ClockVarTargetAssign, driverRange);
            diag << symbol.name;
            diag.addNote(diag::NoteReferencedHere, currRange);
            return false;
        }

        if (curr.isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
            auto& diag = context.addDiag(symbol, diag::LocalFormalVarMultiAssign, driverRange);
            diag << symbol.name;
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
                note << driver.containingSymbol->getHierarchicalPath();
                note << curr.containingSymbol->getHierarchicalPath();
            }
        };

        if (curr.kind == DriverKind::Procedural && driver.kind == DriverKind::Procedural) {
            // Multiple procedural drivers where one of them is an
            // always_comb / always_ff block.
            ProceduralBlockKind procKind;
            if (driver.isInSingleDriverProcedure()) {
                procKind = static_cast<ProceduralBlockKind>(driver.source);
            }
            else {
                procKind = static_cast<ProceduralBlockKind>(curr.source);
                std::swap(driverRange, currRange);
            }

            auto& diag = context.addDiag(symbol, diag::MultipleAlwaysAssigns, driverRange);
            diag << symbol.name << SemanticFacts::getProcedureKindStr(procKind);
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

        auto& diag = context.addDiag(symbol, code, driverRange);
        diag << symbol.name;
        if (isSingleDriverUDNT) {
            SLANG_ASSERT(netType);
            diag << netType->name;
        }

        addAssignedHereNote(diag);
        return false;
    }
};

} // namespace slang::analysis
