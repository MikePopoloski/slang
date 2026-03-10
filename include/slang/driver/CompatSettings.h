//------------------------------------------------------------------------------
//! @file CompatSettings.h
//! @brief Settings for controlling compatibility with other tools
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>

#include "slang/util/Enum.h"

namespace slang {
class DiagnosticEngine;
}

namespace slang::ast {
enum class CompilationFlags;
}

namespace slang::analysis {
enum class AnalysisFlags;
}

namespace slang::driver {

#define COMPAT(x) x(Default) x(Vcs) x(All)
SLANG_ENUM(CompatMode, COMPAT)
#undef COMPAT

/// Collected settings for increasing compatibility with other tools.
class CompatSettings {
public:
    /// Sets the compatibility mode that should be used when calling
    /// other methods on this class.
    void setMode(CompatMode newMode) { mode = newMode; }

    /// Gets the compilation flags implied by the current compat mode.
    std::span<const ast::CompilationFlags> getCompilationFlags() const;

    /// Gets the analysis flags implied by the current compat mode.
    std::span<const analysis::AnalysisFlags> getAnalysisFlags() const;

    /// Configures the given diagnostic engine appropriately for the
    /// current compat mode.
    void configureDiagnostics(DiagnosticEngine& diagEngine) const;

private:
    CompatMode mode = CompatMode::Default;
};

} // namespace slang::driver
