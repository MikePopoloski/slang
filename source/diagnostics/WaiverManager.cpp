//------------------------------------------------------------------------------
// WaiverManager.cpp
// Manages diagnostic waivers from external TOML files
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/WaiverManager.h"

#include <boost_regex.hpp>
#include <fmt/format.h>
#include <fmt/ranges.h>
#include <ranges>
#include <toml++/toml.h>

#include "slang/ast/Symbol.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/text/Glob.h"
#include "slang/text/SourceManager.h"
#include "slang/util/OS.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang {

struct WaiverLinePattern {
    boost::regex regex;

    explicit WaiverLinePattern(const boost::regex& r) : regex(r) {}
};

// Rewrites '.' to '/' so glob wildcards behave correctly on hierarchical
// paths. svGlobMatches is a path-aware glob matcher whose only separator
// is '/': '*' stops at '/' and '...' is what recurses across '/'. A
// literal '...' run in the input is preserved verbatim so users can use
// the LRM-native recursive glob spelling in hier patterns.
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

// Converts user-facing '**' recursive glob syntax to the '...' syntax used
// internally by slang's svGlobMatches. We expose '**' to users because that
// matches widespread tooling convention (gitignore, rg, fd, etc.); '...' is
// accepted too as it's the LRM-native spelling used elsewhere in slang.
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

WaiverRule::WaiverRule() = default;
WaiverRule::~WaiverRule() = default;
WaiverRule::WaiverRule(WaiverRule&&) noexcept = default;
WaiverRule& WaiverRule::operator=(WaiverRule&&) noexcept = default;

template<typename TNode>
static std::string tomlErr(const TNode& node, std::string_view msg) {
    auto& source = node.source();
    return fmt::format("{}:{}:{}: error: {}", *source.path, source.begin.line, source.begin.column,
                       msg);
}

static constexpr std::array KnownKeys = {"file", "hier", "diagnostic", "regex"};

std::string WaiverManager::loadFromFile(const fs::path& path,
                                        const DiagnosticEngine& diagnosticEngine) {
    toml::table root;
#if TOML_EXCEPTIONS
    try {
        root = toml::parse_file(getU8Str(path));
    }
    catch (const toml::parse_error& e) {
        return tomlErr(e, e.description());
    }
#else
    auto parsed = toml::parse_file(getU8Str(path));
    if (!parsed) {
        return tomlErr(parsed.error(), parsed.error().description());
    }
    root = std::move(parsed).table();
#endif

    auto waiversNode = root.get("waivers");
    if (!waiversNode)
        return tomlErr(root, "missing 'waivers' key");

    auto waivers = waiversNode->as_array();
    if (!waivers)
        return tomlErr(*waiversNode, "'waivers' must be an array of tables");

    for (auto& currNode : *waivers) {
        auto entry = currNode.as_table();
        if (!entry)
            return tomlErr(currNode, "waiver entry must be a table");

        // Reject unknown keys so typos in user waiver files surface as load
        // errors instead of silently no-op'ing.
        for (auto& [k, v] : *entry) {
            std::string key(k.str());
            if (std::ranges::find(KnownKeys, key) == KnownKeys.end())
                return tomlErr(k, fmt::format("unknown key '{}'", key));
        }

        // Helper to read a scalar string field with a clear error on bad values.
        std::string errorStr;
        auto readScalar = [&](const char* field, std::string& out) {
            auto node = entry->get(field);
            if (!node)
                return true; // absent is fine - caller decides if required

            auto sv = node->value<std::string>();
            if (!sv) {
                errorStr = tomlErr(*node, fmt::format("'{}' must be a string", field));
                return false;
            }

            out = std::move(*sv);
            return true;
        };

        std::string fileStr, hierStr, regexStr;
        if (!readScalar("file", fileStr) || !readScalar("hier", hierStr) ||
            !readScalar("regex", regexStr)) {
            return errorStr;
        }

        const bool hasFile = !fileStr.empty();
        const bool hasHier = !hierStr.empty();
        if (hasFile && hasHier)
            return tomlErr(*entry, "waiver entry has both 'file' and 'hier'; specify exactly one");

        if (!hasFile && !hasHier)
            return tomlErr(*entry, "waiver entry must have either 'file' or 'hier' as scope");

        WaiverRule rule;
        rule.sourceFile = path;
        rule.sourceLine = entry->source().begin.line;

        if (hasFile) {
            rule.hierScope = false;
            rule.scopeGlob = fileStr;
            rule.normalizedPattern =
                fs::path(convertDoubleStarToEllipsis(fileStr)).lexically_normal();
        }
        else {
            rule.hierScope = true;
            rule.scopeGlob = hierStr;
            rule.normalizedPattern = convertDoubleStarToEllipsis(normalizeDotSep(hierStr));
        }

        // Parse optional diagnostic (string or array of strings)
        if (auto diagNode = entry->get("diagnostic")) {
            std::vector<std::string> names;
            if (auto str = diagNode->value<std::string>()) {
                names.emplace_back(std::move(*str));
            }
            else if (auto arr = diagNode->as_array()) {
                for (size_t j = 0; j < arr->size(); j++) {
                    auto v = (*arr)[j].value<std::string>();
                    if (!v)
                        return tomlErr((*arr)[j], "'diagnostic' list element must be a string");
                    names.push_back(std::move(*v));
                }

                if (names.empty())
                    return tomlErr(*diagNode, "'diagnostic' list must not be empty");
            }
            else {
                return tomlErr(*diagNode, "'diagnostic' must be a string or array of strings");
            }

            for (auto& name : names) {
                if (diagnosticEngine.findFromOptionName(name).empty()) {
                    return tomlErr(*diagNode, fmt::format("unknown diagnostic '{}' (use warning "
                                                          "option names like 'unused-variable')",
                                                          name));
                }
            }

            rule.diagnosticCodes = std::move(names);
        }

        if (!regexStr.empty()) {
            boost::regex compiled(regexStr, boost::regex::no_except);
            if (compiled.status() != 0)
                return tomlErr(*entry, fmt::format("invalid regex '{}'", regexStr));
            rule.linePattern = std::make_unique<WaiverLinePattern>(compiled);
        }

        rules.emplace_back(std::move(rule));
    }

    return {};
}

bool WaiverManager::shouldWaive(const Diagnostic& diagnostic, SourceLocation location,
                                const SourceManager& sourceManager,
                                const DiagnosticEngine& diagnosticEngine) {
    // Per-rule matching pipeline. Invariants for maintainers:
    //   - First match wins (return true on the first all-predicates-pass rule).
    //   - Predicates inside a rule are AND'd in this order: scope, diagnostic
    //     name, regex. The order is chosen cheapest-first, but more importantly
    //     it determines what the rule.scopeMatched / diagnosticMatched bits
    //     mean - they record "we got this far before falling through", which
    //     is what getSummary() reads to explain unused waivers.
    //   - When you add or reorder a predicate, also adjust those bookkeeping
    //     bits so the unused-waivers diagnostics stay accurate.
    //   - We continue updating rule statistics on falls-through (we don't bail
    //     early just because the diagnostic name doesn't match) so that an
    //     "unused" report can distinguish "file matched but diagnostic didn't"
    //     from "file never matched at all."

    // Read once: env-var-based debug switch is process-wide and cannot change
    // between calls - keep it static so the env lookup is paid only once.
    static const bool waiverDebug = !OS::getEnv("SLANG_WAIVER_DEBUG").empty();

    auto buffer = location.buffer();
    if (rules.empty() || !buffer)
        return false;

    std::optional<std::string_view> diagnosticName;
    auto getDiagnosticName = [&]() {
        if (!diagnosticName)
            diagnosticName = diagnosticEngine.getOptionName(diagnostic.code);
        return *diagnosticName;
    };

    // Gather hierarchy information if available. Many diagnostics have no
    // associated symbol (parse errors, preprocessor warnings, top-level
    // semantic checks) and therefore cannot be matched by hier-scoped rules
    // at all - only file scope works for those. The unused-waivers report
    // tries to detect this case below and steer users to file scope.
    auto& filePath = sourceManager.getFullPath(buffer);
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
                                   getDiagnosticName(), getU8Str(filePath),
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

            bool hierMatch = svGlobMatches(normalizeDotSep(hierPath), rule.normalizedPattern);
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
            bool fileMatch = svGlobMatches(filePath.lexically_normal(), rule.normalizedPattern);
            if (waiverDebug) {
                OS::printE(fmt::format("[waiver] rule {} scope=file glob={} file={} fileMatch={}\n",
                                       idx, rule.scopeGlob.generic_string(), getU8Str(filePath),
                                       fileMatch));
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
            SLANG_ASSERT(rule.linePattern);
            auto lineText = sourceManager.getSourceLine(location);
            bool lineMatch = boost::regex_search(lineText.begin(), lineText.end(),
                                                 rule.linePattern->regex);
            if (waiverDebug) {
                OS::printE(fmt::format("[waiver] rule {} regex lineMatch={} text=\"{}\"\n", idx,
                                       lineMatch, lineText));
            }
            if (!lineMatch)
                continue;
        }

        // All checks passed - waive
        rule.appliedCount++;
        if (waiverDebug) {
            OS::printE(fmt::format("[waiver] applied rule {} (scope={})\n", idx,
                                   rule.hierScope ? "hier" : "file"));
        }
        return true;
    }

    return false;
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
        // shouldWaive's evaluation order: scope -> diagnostic name -> regex. If
        // shouldWaive grows a new predicate, add a matching else-branch here so
        // users get an accurate "why" instead of an inappropriate fallback.
        result += "\nUnused waivers:";
        for (const auto& rule : rules) {
            if (rule.appliedCount == 0) {
                std::string file;
                if (rule.sourceFile.empty())
                    file = "<unknown>";
                else if (rule.sourceLine > 0)
                    file = fmt::format("{}:{}", getU8Str(rule.sourceFile), rule.sourceLine);
                else
                    file = getU8Str(rule.sourceFile);

                if (!rule.scopeMatched) {
                    if (rule.hierScope && rule.diagnosticSeenWithoutSymbol) {
                        result += fmt::format(
                            "\n  - {} (diagnostic '{}' has no symbol; hier scope cannot match - "
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
