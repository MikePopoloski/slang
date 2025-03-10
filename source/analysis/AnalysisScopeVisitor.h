//------------------------------------------------------------------------------
// AnalysisScopeVisitor.h
// Internal visitor for analyzing a scope
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/AnalysisDiags.h"
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
    AnalysisManager& manager;
    AnalysisContext& context;
    AnalyzedScope& result;
    const AnalyzedProcedure* parentProcedure;

    AnalysisScopeVisitor(AnalysisManager& manager, AnalysisContext& context, AnalyzedScope& scope,
                         const AnalyzedProcedure* parentProcedure) :
        manager(manager), context(context), result(scope), parentProcedure(parentProcedure) {}

    void visit(const InstanceSymbol& symbol) {
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated))
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
    }

    void visit(const CheckerInstanceSymbol& symbol) {
        // Ignore procedural checkers here; they will be handled by their parent procedure.
        if (symbol.body.flags.has(InstanceFlags::Uninstantiated) || symbol.body.isProcedural)
            return;

        result.childScopes.emplace_back(manager.analyzeSymbol(symbol));
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
    }

    void visit(const GenericClassDefSymbol& symbol) {
        for (auto& spec : symbol.specializations())
            spec.visit(*this);
    }

    void visit(const NetSymbol& symbol) {
        if (symbol.isImplicit) {
            checkValueUnused(symbol, diag::UnusedImplicitNet, diag::UnusedImplicitNet,
                             diag::UnusedImplicitNet);
        }
        else {
            checkValueUnused(symbol, diag::UnusedNet, diag::UndrivenNet, diag::UnusedButSetNet);
        }
    }

    void visit(const VariableSymbol& symbol) {
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
        // For these symbol types we just descend into their members
        // and flatten them into their parent scope.
        visitMembers(symbol);
    }

    // Everything else doesn't need to be analyzed.
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
    void visit(const T&) {}

private:
    template<typename T>
    void visitMembers(const T& symbol) {
        for (auto& member : symbol.members())
            member.visit(*this);
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
};

} // namespace slang::analysis
