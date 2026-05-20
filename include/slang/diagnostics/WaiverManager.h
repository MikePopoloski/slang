//------------------------------------------------------------------------------
//! @file WaiverManager.h
//! @brief Manages diagnostic waivers from external TOML files
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <memory>
#include <string>
#include <vector>

#include "slang/util/Util.h"

namespace slang {

class Diagnostic;
class DiagnosticEngine;
class SourceLocation;
class SourceManager;

/// Opaque holder for a compiled line-content regex. Defined in the .cpp so the
/// boost::regex type doesn't leak into slang's public headers.
struct WaiverLinePattern;

/// Represents a single waiver rule that can suppress diagnostics based on
/// file paths, hierarchy paths, diagnostic names, and source content patterns.
struct SLANG_EXPORT WaiverRule {
    /// True if this is a hierarchy-scoped rule; false for file-scoped.
    bool hierScope = false;

    /// The scope glob as written by the user (for display / diagnostics).
    std::filesystem::path scopeGlob;

    /// The scope glob normalized once at load time for matching.
    /// For file rules: '**' converted to slang's '...' then lexically_normal'd.
    /// For hier rules: '.' replaced with '/' then '**' converted to '...'.
    std::filesystem::path normalizedPattern;

    /// Optional source line content pattern (regex). Matched with regex_search
    /// (substring), not regex_match - anchor with ^ / $ if you need full-line.
    std::unique_ptr<WaiverLinePattern> linePattern;

    /// Optional diagnostic code names (e.g., "unused-variable").
    /// Empty means match all diagnostics; one or more entries means match any in the list.
    /// Names are validated against DiagnosticEngine::findFromOptionName at load time, so
    /// any value present here is guaranteed to correspond to a real diagnostic option.
    std::vector<std::string> diagnosticCodes;

    /// Number of times this rule has suppressed a diagnostic.
    size_t appliedCount = 0;

    // The next three flags exist purely to drive the "why was this waiver unused?"
    // explanation in WaiverManager::getSummary. They are NOT used as fast-paths
    // during matching. shouldWaive() must keep them in sync with the corresponding
    // predicate decision points; if you add a new predicate, add a sibling flag.

    /// Whether the scope glob (file or hier) matched at least once.
    bool scopeMatched = false;

    /// Whether scope + diagnostic name both matched at least once.
    bool diagnosticMatched = false;

    /// The path of the waiver file this rule was loaded from.
    std::filesystem::path sourceFile;

    /// 1-based line in sourceFile where the [[waivers]] entry begins,
    /// or 0 if the load source didn't carry position info.
    uint32_t sourceLine = 0;

    /// For hier-scoped rules with a diagnostic filter: set when the named
    /// diagnostic was issued but had no symbol attached, so the rule could
    /// not match. This typically happens for parse/preprocess/lex diagnostics
    /// (no AST symbol exists yet) and for some elaboration-time diagnostics
    /// that are reported against a SourceLocation rather than attached to a
    /// Symbol. Used to suggest switching to a 'file' scope in the unused-
    /// waivers report rather than emitting the generic "no hierarchy paths
    /// matched glob" message.
    bool diagnosticSeenWithoutSymbol = false;

    WaiverRule();
    ~WaiverRule();
    WaiverRule(WaiverRule&&) noexcept;
    WaiverRule& operator=(WaiverRule&&) noexcept;

    /// Check if a file path matches this rule's file pattern (file-scoped rules only)
    [[nodiscard]] bool matchesFile(const std::filesystem::path& filePath) const;

    /// Check if source line content matches this rule's line pattern.
    /// Caller must ensure linePattern is set before calling.
    [[nodiscard]] bool matchesLineContent(std::string_view lineContent) const;

    /// Check if a hierarchical path matches this rule's hier glob (hier-scoped rules only)
    [[nodiscard]] bool matchesHier(std::string_view hierPath) const;
};

/// The WaiverManager loads and manages diagnostic waiver rules from external
/// TOML files. It provides the ability to suppress diagnostics based on flexible
/// matching criteria including file paths, hierarchy paths, diagnostic names,
/// and source content patterns.
///
/// Evaluation model (see shouldWaive()):
///   - Rules are evaluated in load order; the FIRST rule whose predicates all
///     match wins. There is no priority/specificity scheme and no "deny"
///     counterpart - a waiver can only suppress, never re-enable.
///   - For a single rule, all configured predicates are AND'd: scope (file or
///     hier), then optional diagnostic-name filter, then optional regex.
///   - Waivers run AFTER -W severity remapping and --ignore-paths in
///     DiagnosticEngine::issueImpl, so a waiver cannot promote a warning to an
///     error and cannot resurrect a diagnostic already suppressed elsewhere.
///
/// Extending the schema: when adding a new TOML key, update the `knownKeys`
/// allowlist in loadFromFile (otherwise it will be rejected as a typo) and add
/// matching state to WaiverRule plus a corresponding predicate in shouldWaive.
///
/// Threading: like DiagnosticEngine, instances are not synchronized. Callers
/// must ensure shouldWaive() is invoked single-threaded, which is the
/// contract DiagnosticEngine::issue() already imposes.
///
/// Debugging: set the SLANG_WAIVER_DEBUG environment variable to any non-empty
/// value to get per-rule trace output on stderr from shouldWaive().
///
/// Example TOML format:
///
/// @code
/// [[waivers]]
/// file = "ip/**"                          # waive all diagnostics in these files
///
/// [[waivers]]
/// file = "tb/**/*.sv"
/// diagnostic = ["unused-variable", "width-trunc"]
///
/// [[waivers]]
/// file = "rtl/core.sv"                    # waive specific occurrence via line content
/// diagnostic = "unused-variable"
/// regex = '\bdebug_reg\b'                  # literal string: no escape soup
///
/// [[waivers]]
/// hier = "top/u_subsys/u_conv"            # waive by hierarchy
/// diagnostic = "width-trunc"
///
/// [[waivers]]
/// hier = "**/u_debug*"
/// diagnostic = "unused-variable"
/// regex = '\bdbg_status\b'
/// @endcode
///
class SLANG_EXPORT WaiverManager {
public:
    WaiverManager() = default;

    /// Load waiver rules from a TOML file, appending to any already loaded.
    /// Multiple loads are purely additive - there is no de-dup, no override,
    /// and load order determines the first-match-wins precedence used by
    /// shouldWaive(). On parse failure rules already accepted from prior calls
    /// are preserved; rules from the failing file are not partially applied
    /// because each rule is push_back'd only after the entry fully validates.
    /// @param path The path to the TOML waiver file
    /// @param diagnosticEngine Used to validate diagnostic option names at load time
    ///        (so misspelled diagnostic names fail loudly instead of silently
    ///        never matching). Warning options must already be configured on
    ///        the engine before this call so that user-defined groups resolve.
    /// @param errors Output parameter for error messages (if any)
    /// @return true if the file was loaded successfully, false otherwise
    [[nodiscard]] bool loadFromFile(const std::filesystem::path& path,
                                    const DiagnosticEngine& diagnosticEngine, std::string& errors);

    /// Check if a diagnostic should be waived based on the loaded rules.
    /// Returns true on the FIRST rule that matches; later rules are not
    /// consulted (so order is significant). Side effect: updates per-rule
    /// statistics on every call regardless of result, including on partial
    /// matches that later predicates reject - these stats feed getSummary().
    /// @param diagnostic The diagnostic to check
    /// @param location The source location of the diagnostic
    /// @param sourceManager The source manager for accessing file information
    /// @param diagnosticEngine The diagnostic engine for accessing diagnostic metadata
    /// @return true if the diagnostic should be waived (suppressed), false otherwise
    [[nodiscard]] bool shouldWaive(const Diagnostic& diagnostic, SourceLocation location,
                                   const SourceManager& sourceManager,
                                   const DiagnosticEngine& diagnosticEngine);

    /// Get how many times waivers were applied.
    [[nodiscard]] size_t getAppliedCount() const;

    /// Get how many rules were never hit.
    [[nodiscard]] size_t getUnusedCount() const;

    /// Render a summary of unused waivers for logging.
    [[nodiscard]] std::string getSummary(bool showUnused = false) const;

private:
    std::vector<WaiverRule> rules;

    /// Helper to get the source line text at a given location. The returned
    /// view is backed by @a sourceManager and is valid for as long as it is.
    [[nodiscard]] std::string_view getLineText(SourceLocation location,
                                               const SourceManager& sourceManager) const;
};

} // namespace slang
