//------------------------------------------------------------------------------
// CompatSettings.cpp
// Settings for controlling compatibility with other tools
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/CompatSettings.h"

#include "slang/analysis/AnalysisOptions.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LexerDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::driver {

using namespace ast;
using namespace analysis;

// clang-format off
#define VCS_COMP_FLAGS \
    CompilationFlags::AllowHierarchicalConst, \
    CompilationFlags::RelaxEnumConversions, \
    CompilationFlags::AllowUseBeforeDeclare, \
    CompilationFlags::RelaxStringConversions, \
    CompilationFlags::AllowRecursiveImplicitCall, \
    CompilationFlags::AllowBareValParamAssignment, \
    CompilationFlags::AllowSelfDeterminedStreamConcat, \
    CompilationFlags::AllowMergingAnsiPorts

static constexpr CompilationFlags vcsCompFlags[] = {VCS_COMP_FLAGS};
static constexpr CompilationFlags allCompFlags[] = {
    VCS_COMP_FLAGS,
    CompilationFlags::AllowTopLevelIfacePorts,
    CompilationFlags::AllowUnnamedGenerate,
    CompilationFlags::AllowVirtualIfaceWithOverride
};

#define VCS_ANALYSIS_FLAGS \
    AnalysisFlags::AllowMultiDrivenLocals

static constexpr AnalysisFlags vcsAnalysisFlags[] = {VCS_ANALYSIS_FLAGS};
static constexpr AnalysisFlags allAnalysisFlags[] = {
    VCS_ANALYSIS_FLAGS,
    AnalysisFlags::AllowDupInitialDrivers
};
// clang-format on

std::span<const CompilationFlags> CompatSettings::getCompilationFlags() const {
    switch (mode) {
        case CompatMode::Default:
            return {};
        case CompatMode::Vcs:
            return vcsCompFlags;
        case CompatMode::All:
            return allCompFlags;
    }
    SLANG_UNREACHABLE;
}

std::span<const AnalysisFlags> CompatSettings::getAnalysisFlags() const {
    switch (mode) {
        case CompatMode::Default:
            return {};
        case CompatMode::Vcs:
            return vcsAnalysisFlags;
        case CompatMode::All:
            return allAnalysisFlags;
    }
    SLANG_UNREACHABLE;
}

void CompatSettings::configureDiagnostics(DiagnosticEngine& diagEngine) const {
    // Some tools violate the standard in various ways, but in order to allow
    // compatibility with these tools we change the respective errors into a
    // suppressible warning that we promote to an error by default. This allows
    // the user to turn this back into a warning, or turn it off altogether.

    if (mode != CompatMode::All) {
        for (auto d : {
                 diag::DuplicateDefinition,
                 diag::BadProceduralForce,
                 diag::UnknownSystemName,
                 diag::NonstandardHierarchicalCross,
                 diag::NonstandardStringConcat,
                 diag::MixedVarAssigns,
                 diag::MultipleContAssigns,
                 diag::MultipleAlwaysAssigns,
                 diag::MisplacedTrailingSeparator,
                 diag::InitializerRequired,
             }) {
            diagEngine.setBaselineSeverity(d, DiagnosticSeverity::Error);
        }
    }

    if (mode == CompatMode::Vcs || mode == CompatMode::All) {
        // Ignore these warnings by default in compat mode.
        for (auto d : {
                 diag::StaticInitializerMustBeExplicit,
                 diag::ImplicitConvert,
                 diag::BadFinishNum,
                 diag::NonstandardSysFunc,
                 diag::NonstandardForeach,
                 diag::NonstandardDist,
                 diag::NestedBlockComment,
             }) {
            diagEngine.setBaselineSeverity(d, DiagnosticSeverity::Ignored);
        }
    }
    else {
        // These warnings are set to Error severity by default, unless we're in vcs compat mode.
        // The user can always downgrade via warning options.
        for (auto d : {
                 diag::IndexOOB,
                 diag::RangeOOB,
                 diag::RangeWidthOOB,
                 diag::ImplicitNamedPortTypeMismatch,
                 diag::SplitDistWeightOp,
                 diag::DPIPureTask,
                 diag::SpecifyPathConditionExpr,
                 diag::SolveBeforeDisallowed,
                 diag::DynamicNotProcedural,
                 diag::QualifiersOnOutOfBlock,
                 diag::MemberImplNotFound,
                 diag::InitializerRequired,
             }) {
            diagEngine.setBaselineSeverity(d, DiagnosticSeverity::Error);
        }
    }
}

} // namespace slang::driver
