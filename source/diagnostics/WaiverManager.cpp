//------------------------------------------------------------------------------
// WaiverManager.cpp
// Manages diagnostic waivers from external TOML files
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#if defined(__GNUC__) && !defined(__clang__)
// GCC spuriously warns about a zero-size allocation inside libstdc++'s <regex> 
// headers when this file is built at -O2 or higher, see GCC PR 116332.
// #pragma GCC diagnostic ignored "-Walloc-zero" around the call site doesn't 
// help — the warning is emitted from an optimisation pass against the libstdc++
// header location, outside any pragma scope at the call site.
#    pragma GCC optimize("-O1")
#endif

#include "slang/diagnostics/WaiverManager.h"

#include <fmt/format.h>
#include <fmt/ranges.h>
#include <ranges>

// Disable exceptions in toml++ so slang still builds when configured without
// exception support.
#define TOML_EXCEPTIONS 0
#include <toml++/toml.h>

#include "slang/ast/Symbol.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/text/Glob.h"
#include "slang/text/SourceManager.h"
#include "slang/util/OS.h"

namespace slang {

/// Rewrite '.' to '/' so glob wildcards behave correctly on hierarchical
/// paths. svGlobMatches is a path-aware glob matcher whose only separator
/// is '/': '*' stops at '/' and '...' is what recurses across '/'. A
/// literal '...' run in the input is preserved verbatim so users can use
/// the LRM-native recursive glob spelling in hier patterns.
static std::string normalizeDotSep(std::string_view s) {
    std::string result;
    result.reserve(s.size());
    for (size_t i = 0; i < s.size(); i++) {
        if (s[i] == '.' && i + 2 < s.size() && s[i + 1] == '.' && s[i + 2] == '.') {
            result += "...";
            i += 2;
        }
        else if (s[i] == '.') {
            result += '/';
        }
        else {
            result += s[i];
        }
    }
    return result;
}

/// Convert user-facing '**' recursive glob syntax to the '...' syntax used
/// internally by slang's svGlobMatches. We expose '**' to users because that
/// matches widespread tooling convention (gitignore, rg, fd, etc.); '...' is
/// accepted too as it's the LRM-native spelling used elsewhere in slang.
static std::string convertDoubleStarToEllipsis(std::string_view s) {
    std::string result;
    result.reserve(s.size());
    for (size_t i = 0; i < s.size(); i++) {
        if (s[i] == '*' && i + 1 < s.size() && s[i + 1] == '*') {
            result += "...";
            i++; // skip second '*'
        }
        else {
            result += s[i];
        }
    }
    return result;
}

bool WaiverRule::matchesFile(const std::filesystem::path& filePath) const {
    return svGlobMatches(filePath.lexically_normal(), normalizedPattern);
}

bool WaiverRule::matchesLineContent(std::string_view lineContent) const {
    SLANG_ASSERT(linePattern);
#if __cpp_exceptions
    try {
        return std::regex_search(lineContent.begin(), lineContent.end(), *linePattern);
    }
    catch (const std::regex_error&) {
        return false;
    }
#else
    // Under -fno-exceptions a regex error aborts; pre-validation at load
    // time keeps that unreachable in practice for well-formed patterns.
    return std::regex_search(lineContent.begin(), lineContent.end(), *linePattern);
#endif
}

bool WaiverRule::matchesHier(std::string_view hierPath) const {
    return svGlobMatches(std::filesystem::path(normalizeDotSep(hierPath)), normalizedPattern);
}

bool WaiverManager::loadFromFile(const std::filesystem::path& path,
                                 const DiagnosticEngine& diagnosticEngine, std::string& errors) {
    toml::parse_result parsed = toml::parse_file(path.string());
    if (!parsed) {
        const auto& err = parsed.error();
        errors = fmt::format("TOML parsing error: {}", std::string_view(err.description()));
        return false;
    }

    const toml::table& root = parsed.table();

    const toml::node* waiversNode = root.get("waivers");
    if (!waiversNode) {
        errors = "Missing 'waivers' key in TOML file";
        return false;
    }

    const toml::array* waivers = waiversNode->as_array();
    if (!waivers) {
        errors = "'waivers' must be an array of tables";
        return false;
    }

    for (size_t i = 0; i < waivers->size(); i++) {
        const toml::table* entry = (*waivers)[i].as_table();
        if (!entry) {
            errors = fmt::format("Waiver entry {} must be a table", i);
            return false;
        }

        // Reject unknown keys so typos in user waiver files surface as load
        // errors instead of silently no-op'ing. When adding a new TOML key,
        // append it here AND add a corresponding field to WaiverRule plus a
        // predicate in shouldWaive — otherwise the new key will be accepted
        // by the parser but never enforced at match time.
        static const std::array knownKeys = {"file", "hier", "diagnostic", "regex"};
        for (auto&& [k, v] : *entry) {
            std::string key(k.str());
            if (std::ranges::find(knownKeys, key) == knownKeys.end()) {
                errors = fmt::format("Unknown key '{}' in waiver entry {}", key, i);
                return false;
            }
        }

        // Helper to read a scalar string field with a clear error on bad values.
        auto readScalar = [&](const char* field, std::string& out) -> bool {
            const toml::node* node = entry->get(field);
            if (!node)
                return true; // absent is fine — caller decides if required
            auto sv = node->value<std::string>();
            if (!sv) {
                errors = fmt::format("Waiver entry {}: '{}' must be a string", i, field);
                return false;
            }
            out = std::move(*sv);
            return true;
        };

        std::string fileStr, hierStr, regexStr;
        if (!readScalar("file", fileStr) || !readScalar("hier", hierStr) ||
            !readScalar("regex", regexStr)) {
            return false;
        }

        bool hasFile = !fileStr.empty();
        bool hasHier = !hierStr.empty();

        if (hasFile && hasHier) {
            errors = fmt::format("Waiver entry {} has both 'file' and 'hier'; specify exactly one",
                                 i);
            return false;
        }
        if (!hasFile && !hasHier) {
            errors = fmt::format("Waiver entry {} must have either 'file' or 'hier' as scope", i);
            return false;
        }

        WaiverRule rule;
        rule.sourceFile = path;
        rule.sourceLine = entry->source().begin.line;

        if (hasFile) {
            rule.hierScope = false;
            rule.scopeGlob = fileStr;
            rule.normalizedPattern =
                std::filesystem::path(convertDoubleStarToEllipsis(fileStr)).lexically_normal();
        }
        else {
            rule.hierScope = true;
            rule.scopeGlob = hierStr;
            rule.normalizedPattern = convertDoubleStarToEllipsis(normalizeDotSep(hierStr));
        }

        // Parse optional diagnostic (string or array of strings)
        if (const toml::node* diagNode = entry->get("diagnostic")) {
            std::vector<std::string> names;
            if (auto str = diagNode->value<std::string>(); str) {
                names.push_back(std::move(*str));
            }
            else if (const toml::array* arr = diagNode->as_array()) {
                for (size_t j = 0; j < arr->size(); j++) {
                    auto v = (*arr)[j].value<std::string>();
                    if (!v) {
                        errors = fmt::format(
                            "Waiver entry {}: 'diagnostic' list element {} must be a string", i, j);
                        return false;
                    }
                    names.push_back(std::move(*v));
                }
                if (names.empty()) {
                    errors = fmt::format("Waiver entry {}: 'diagnostic' list must not be empty", i);
                    return false;
                }
            }
            else {
                errors = fmt::format(
                    "Waiver entry {}: 'diagnostic' must be a string or array of strings", i);
                return false;
            }

            for (const auto& name : names) {
                if (diagnosticEngine.findFromOptionName(name).empty()) {
                    errors = fmt::format("Unknown diagnostic '{}' in entry {} (use warning "
                                         "option names like 'unused-variable')",
                                         name, i);
                    return false;
                }
            }

            rule.diagnosticCodes = std::move(names);
        }

        // Parse optional regex
        if (!regexStr.empty()) {
#if __cpp_exceptions
            try {
                rule.linePattern = std::regex(regexStr, std::regex::ECMAScript);
            }
            catch (const std::regex_error& e) {
                errors = fmt::format("Invalid regex in entry {}: {}", i, e.what());
                return false;
            }
#else
            // std::regex has no non-throwing ctor; an invalid pattern aborts.
            rule.linePattern = std::regex(regexStr, std::regex::ECMAScript);
#endif
        }

        rules.push_back(std::move(rule));
    }

    return true;
}

bool WaiverManager::shouldWaive(const Diagnostic& diagnostic, SourceLocation location,
                                const SourceManager& sourceManager,
                                const DiagnosticEngine& diagnosticEngine) {
    // Per-rule matching pipeline. Invariants for maintainers:
    //   - First match wins (return true on the first all-predicates-pass rule).
    //   - Predicates inside a rule are AND'd in this order: scope, diagnostic
    //     name, regex. The order is chosen cheapest-first, but more importantly
    //     it determines what the rule.scopeMatched / diagnosticMatched bits
    //     mean — they record "we got this far before falling through", which
    //     is what getSummary() reads to explain unused waivers.
    //   - When you add or reorder a predicate, also adjust those bookkeeping
    //     bits so the unused-waivers diagnostics stay accurate.
    //   - We continue updating rule statistics on falls-through (we don't bail
    //     early just because the diagnostic name doesn't match) so that an
    //     "unused" report can distinguish "file matched but diagnostic didn't"
    //     from "file never matched at all."

    // Read once: env-var-based debug switch is process-wide and cannot change
    // between calls — keep it static so the env lookup is paid only once.
    static const bool waiverDebug = !OS::getEnv("SLANG_WAIVER_DEBUG").empty();

    if (rules.empty() || !location)
        return false;

    // Get file path
    auto buffer = location.buffer();
    if (!buffer)
        return false;

    const std::filesystem::path& filePath = sourceManager.getFullPath(buffer);

    bool diagnosticNameInitialized = false;
    std::string_view diagnosticName;
    auto getDiagnosticName = [&]() -> std::string_view {
        if (!diagnosticNameInitialized) {
            diagnosticName = diagnosticEngine.getOptionName(diagnostic.code);
            diagnosticNameInitialized = true;
        }
        return diagnosticName;
    };

    // Gather hierarchy information if available. Many diagnostics have no
    // associated symbol (parse errors, preprocessor warnings, top-level
    // semantic checks) and therefore cannot be matched by hier-scoped rules
    // at all — only file scope works for those. The unused-waivers report
    // tries to detect this case below and steer users to file scope.
    std::string hierPath;
    if (diagnostic.symbol) {
        // A symbol detached from the AST (no parent scope) has no meaningful
        // hierarchical path; treat it as if it had no symbol for matching.
        if (diagnostic.symbol->getParentScope())
            hierPath = diagnostic.symbol->getHierarchicalPath();
    }
    else if (waiverDebug) {
        bool ruleHasHierScope = std::ranges::any_of(rules, [](const WaiverRule& r) {
            return r.hierScope;
        });
        if (ruleHasHierScope) {
            OS::printE(fmt::format("[waiver] diag '{}' has no symbol/hier; hier-scoped rules "
                                   "cannot match (file={} line={})\n",
                                   getDiagnosticName(), filePath.generic_string(),
                                   sourceManager.getLineNumber(location)));
        }
    }

    // Check each rule
    for (size_t idx = 0; idx < rules.size(); idx++) {
        auto& rule = rules[idx];

        if (rule.hierScope) {
            // Hier-scoped rule: match hierarchy path
            if (hierPath.empty()) {
                // If this rule names the diagnostic but the diagnostic has no
                // symbol/hier info, record that so the unused-waivers report
                // can give a precise hint instead of the generic "no hier
                // paths matched" message.
                if (!rule.diagnosticCodes.empty()) {
                    auto name = getDiagnosticName();
                    if (std::ranges::find(rule.diagnosticCodes, name) !=
                        rule.diagnosticCodes.end()) {
                        rule.diagnosticSeenWithoutSymbol = true;
                    }
                }
                continue;
            }

            bool hierMatch = rule.matchesHier(hierPath);
            if (waiverDebug) {
                OS::printE(
                    fmt::format("[waiver] rule {} scope=hier glob={} hierPath={} hierMatch={}\n",
                                idx, rule.scopeGlob.generic_string(), hierPath, hierMatch));
            }
            if (!hierMatch)
                continue;

            rule.scopeMatched = true;
        }
        else {
            // File-scoped rule: match file path
            bool fileMatch = rule.matchesFile(filePath);
            if (waiverDebug) {
                OS::printE(fmt::format("[waiver] rule {} scope=file glob={} file={} fileMatch={}\n",
                                       idx, rule.scopeGlob.generic_string(),
                                       filePath.generic_string(), fileMatch));
            }
            if (!fileMatch)
                continue;

            rule.scopeMatched = true;
        }

        // Check diagnostic filter
        if (!rule.diagnosticCodes.empty()) {
            auto name = getDiagnosticName();
            bool found = std::ranges::find(rule.diagnosticCodes, name) !=
                         rule.diagnosticCodes.end();
            if (waiverDebug && !found) {
                OS::printE(fmt::format("[waiver] rule {} diagFilter=[{}] actual={} -> no match\n",
                                       idx, fmt::join(rule.diagnosticCodes, ","), name));
            }
            if (!found)
                continue;
        }

        rule.diagnosticMatched = true;

        // Check regex filter
        if (rule.linePattern) {
            std::string_view lineText = getLineText(location, sourceManager);
            bool lineMatch = rule.matchesLineContent(lineText);
            if (waiverDebug) {
                OS::printE(fmt::format("[waiver] rule {} regex lineMatch={} text=\"{}\"\n", idx,
                                       lineMatch, lineText));
            }
            if (!lineMatch)
                continue;
        }

        // All checks passed — waive
        rule.appliedCount++;
        if (waiverDebug) {
            OS::printE(fmt::format("[waiver] applied rule {} (scope={})\n", idx,
                                   rule.hierScope ? "hier" : "file"));
        }
        return true;
    }

    return false;
}

std::string_view WaiverManager::getLineText(SourceLocation location,
                                            const SourceManager& sourceManager) const {
    // Returns the raw source line containing `location`, with no transformation:
    // tabs are not expanded, leading/trailing whitespace is preserved, and the
    // text is treated as raw bytes (UTF-8 sequences are passed through, not
    // decoded). The returned view is what user-supplied regexes match against,
    // so any user surprise about anchoring or character classes likely traces
    // back to that raw-bytes contract.
    return sourceManager.getSourceLine(location);
}

size_t WaiverManager::getAppliedCount() const {
    size_t applied = 0;
    for (const auto& rule : rules)
        applied += rule.appliedCount;
    return applied;
}

size_t WaiverManager::getUnusedCount() const {
    size_t unused = 0;
    for (const auto& rule : rules) {
        if (rule.appliedCount == 0)
            unused++;
    }
    return unused;
}

static std::string describeDiags(const WaiverRule& rule) {
    if (rule.diagnosticCodes.empty())
        return "*";
    return fmt::format("{}", fmt::join(rule.diagnosticCodes, ","));
}

static std::string describeRule(const WaiverRule& rule) {
    return fmt::format("{}=\"{}\" diag={}", rule.hierScope ? "hier" : "file",
                       rule.scopeGlob.generic_string(), describeDiags(rule));
}

std::string WaiverManager::getSummary(bool showUnused) const {
    auto unused = getUnusedCount();

    if (unused == 0)
        return {};

    std::string result = fmt::format("warning: {} unused waiver{}", unused, unused == 1 ? "" : "s");
    if (!showUnused) {
        result += " (rerun with --print-unused-waivers to list)";
    }
    else {
        // For each unused rule, pick the most specific reason we can. The cases
        // below are ordered "earliest predicate that failed" first, mirroring
        // shouldWaive's evaluation order: scope → diagnostic name → regex. If
        // shouldWaive grows a new predicate, add a matching else-branch here so
        // users get an accurate "why" instead of an inappropriate fallback.
        result += "\nUnused waivers:";
        for (const auto& rule : rules) {
            if (rule.appliedCount == 0) {
                std::string file;
                if (rule.sourceFile.empty())
                    file = "<unknown>";
                else if (rule.sourceLine > 0)
                    file = fmt::format("{}:{}", rule.sourceFile.string(), rule.sourceLine);
                else
                    file = rule.sourceFile.string();
                if (!rule.scopeMatched) {
                    if (rule.hierScope && rule.diagnosticSeenWithoutSymbol) {
                        result += fmt::format(
                            "\n  - {} (diagnostic '{}' has no symbol; hier scope cannot match — "
                            "use 'file' scope) [{}]",
                            describeRule(rule), describeDiags(rule), file);
                    }
                    else {
                        result += fmt::format("\n  - {} (no {} matched glob) [{}]",
                                              describeRule(rule),
                                              rule.hierScope ? "hierarchy paths" : "files", file);
                    }
                }
                else if (!rule.diagnosticMatched) {
                    result += fmt::format("\n  - {} (diagnostic '{}' not seen in matching {}) [{}]",
                                          describeRule(rule), describeDiags(rule),
                                          rule.hierScope ? "instances" : "files", file);
                }
                else {
                    result += fmt::format("\n  - {} (regex never matched source content) [{}]",
                                          describeRule(rule), file);
                }
            }
        }
    }

    return result;
}

} // namespace slang
