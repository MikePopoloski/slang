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
#include "slang/diagnostics/DiagnosticEngine.h"

namespace slang {

// Defined in the generated DiagCode.cpp file.
std::span<const std::pair<DiagCode, DiagnosticSeverity>> findCompatDiagSeverities(
    std::string_view mode);

} // namespace slang

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
    CompilationFlags::AllowMergingAnsiPorts, \
    CompilationFlags::AllowArrayConcatAssignPattern, \
    CompilationFlags::AllowLibModuleRedefinition, \
    CompilationFlags::AllowCrossAutoBinMax, \
    CompilationFlags::InferInputPortsAsVars

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
    // The per-mode severity overrides are defined in diagnostics.txt.
    for (auto [code, severity] : findCompatDiagSeverities(toString(mode)))
        diagEngine.setBaselineSeverity(code, severity);
}

} // namespace slang::driver
