//------------------------------------------------------------------------------
//! @file TimeTrace.h
//! @brief Time tracing for profiling performance
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <iosfwd>
#include <memory>
#include <string>

#include "slang/util/Function.h"
#include "slang/util/Util.h"

namespace slang {

/// Support for performance profiling via hierarchical time tracing.
/// Record events with @a beginTrace and @a endTrace and then dump the
/// results to file with @a write for viewing with the Chrome Profiler.
class SLANG_EXPORT TimeTrace {
public:
    /// Indicates whether tracing has been enabled or not.
    static bool isEnabled() { return profiler != nullptr; }

    /// Initializes time tracing support.
    static void initialize();

    /// Writes the results of time tracing to the given stream.
    /// The output is JSON, in Chrome "Trace Event" format, see
    /// https://docs.google.com/document/d/1CvAClvFfyA5R-PhYUmn5OOQtYMH4h6I0nSsKchNAySU/preview
    static void write(std::ostream& os);

    /// Starts tracing a section.
    /// @param name the name of the section
    /// @param detail extra details to include in the trace about the section
    static void beginTrace(std::string_view name, std::string_view detail);

    /// Starts tracing a section.
    /// @param name the name of the section
    /// @param detail extra details to include in the trace about the section
    static void beginTrace(std::string_view name, function_ref<std::string()> detail);

    /// Ends tracing a section previously started by @a beginTrace
    static void endTrace();

private:
    TimeTrace() = delete;

    struct Profiler;
    static std::unique_ptr<Profiler> profiler;
};

/// A helper class that calls begin and end of the time trace profiler.
/// When the object is constructed, it begins the trace section and when
/// it is destroyed, it stops it. If the time profiler is not initialized
/// the overhead is a single branch.
class SLANG_EXPORT
TimeTraceScope{public: TimeTraceScope(std::string_view name, std::string_view detail){
    if (TimeTrace::isEnabled()) TimeTrace::beginTrace(name, detail);
} // namespace slang

TimeTraceScope(std::string_view name, function_ref<std::string()> detail) {
    if (TimeTrace::isEnabled())
        TimeTrace::beginTrace(name, detail);
}

~TimeTraceScope() {
    if (TimeTrace::isEnabled())
        TimeTrace::endTrace();
}
}
;

} // namespace slang
