//------------------------------------------------------------------------------
// DiagnosticEngine.cpp
// Primary interface for managing diagnostic reporting
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticEngine.h"

#include <algorithm>
#include <fmt/args.h>

#include "slang/diagnostics/DiagArgFormatter.h"
#include "slang/diagnostics/DiagnosticClient.h"
#include "slang/diagnostics/MetaDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/text/Glob.h"
#include "slang/text/SourceManager.h"
#include "slang/util/SmallMap.h"

namespace fs = std::filesystem;

namespace slang {

// These are defined in the generated DiagCode.cpp file.
std::string_view getDefaultMessage(DiagCode code);
DiagnosticSeverity getDefaultSeverity(DiagCode code);
std::string_view getDefaultOptionName(DiagCode code);
std::span<const DiagCode> findDiagsFromOptionName(std::string_view name);
const DiagGroup* findDefaultDiagGroup(std::string_view name);

DiagnosticEngine::SymbolPathCB DiagnosticEngine::defaultSymbolPathCB;
DiagnosticEngine::FormatterMap DiagnosticEngine::defaultFormatters;

DiagnosticEngine::DiagnosticEngine(const SourceManager& sourceManager) :
    sourceManager(sourceManager), symbolPathCB(defaultSymbolPathCB), formatters(defaultFormatters) {
}

DiagnosticEngine::~DiagnosticEngine() = default;

void DiagnosticEngine::addClient(const std::shared_ptr<DiagnosticClient>& client) {
    client->setEngine(*this);
    clients.push_back(client);
}

void DiagnosticEngine::clearClients() {
    clients.clear();
}

void DiagnosticEngine::clearCounts() {
    numErrors = 0;
    numWarnings = 0;
    clients.clear();
}

void DiagnosticEngine::setSeverity(DiagCode code, DiagnosticSeverity severity) {
    severityTable[code] = severity;
}

DiagnosticSeverity DiagnosticEngine::getSeverity(DiagCode code, SourceLocation location) const {
    // Check if we have an in-source severity configured.
    if (auto sev = findMappedSeverity(code, location); sev.has_value())
        return *sev;

    if (auto it = severityTable.find(code); it != severityTable.end())
        return it->second;

    auto result = getDefaultSeverity(code);
    switch (result) {
        case DiagnosticSeverity::Ignored:
            break;
        case DiagnosticSeverity::Note:
            if (ignoreAllNotes)
                return DiagnosticSeverity::Ignored;
            break;
        case DiagnosticSeverity::Warning:
            if (ignoreAllWarnings)
                return DiagnosticSeverity::Ignored;
            if (warningsAsErrors)
                return DiagnosticSeverity::Error;
            break;
        case DiagnosticSeverity::Error:
            if (errorsAsFatal)
                return DiagnosticSeverity::Fatal;
            break;
        case DiagnosticSeverity::Fatal:
            if (fatalsAsErrors)
                return DiagnosticSeverity::Error;
            break;
    }
    return result;
}

void DiagnosticEngine::setMessage(DiagCode code, const std::string& message) {
    messageTable[code] = message;
}

std::string_view DiagnosticEngine::getMessage(DiagCode code) const {
    if (auto it = messageTable.find(code); it != messageTable.end())
        return it->second;
    return getDefaultMessage(code);
}

std::string_view DiagnosticEngine::getOptionName(DiagCode code) const {
    return getDefaultOptionName(code);
}

std::span<const DiagCode> DiagnosticEngine::findFromOptionName(std::string_view optionName) const {
    return findDiagsFromOptionName(optionName);
}

const DiagGroup* DiagnosticEngine::findDiagGroup(std::string_view name) const {
    return findDefaultDiagGroup(name);
}

void DiagnosticEngine::clearMappings() {
    severityTable.clear();
    messageTable.clear();
}

void DiagnosticEngine::clearMappings(DiagnosticSeverity severity) {
    erase_if(severityTable, [severity](auto& pair) { return pair.second == severity; });
}

std::error_code DiagnosticEngine::addIgnorePaths(std::string_view pattern) {
    std::error_code ec;
    if (pattern.starts_with("..."sv)) {
        ignoreWarnPatterns.emplace_back(pattern);
        return ec;
    }

    auto p = fs::weakly_canonical(pattern, ec);
    if (!ec)
        ignoreWarnPatterns.emplace_back(std::move(p));

    return ec;
}

std::error_code DiagnosticEngine::addIgnoreMacroPaths(std::string_view pattern) {
    std::error_code ec;
    if (pattern.starts_with("..."sv)) {
        ignoreMacroWarnPatterns.emplace_back(pattern);
        return ec;
    }

    auto p = fs::weakly_canonical(pattern, ec);
    if (!ec)
        ignoreMacroWarnPatterns.emplace_back(std::move(p));

    return ec;
}

// Checks that all of the given ranges are in the same macro argument expansion as `loc`
static bool checkMacroArgRanges(const DiagnosticEngine& engine, SourceLocation loc,
                                std::span<const SourceRange> ranges) {
    const SourceManager& sm = engine.getSourceManager();
    if (!sm.isMacroArgLoc(loc))
        return false;

    loc = sm.getExpansionLoc(loc);

    SmallVector<SourceRange, 8> mappedRanges;
    engine.mapSourceRanges(loc, ranges, mappedRanges, false);

    if (ranges.size() > mappedRanges.size())
        return false;

    for (auto& range : mappedRanges) {
        SLANG_ASSERT(range.start().buffer() == loc.buffer());
        SLANG_ASSERT(range.end().buffer() == loc.buffer());

        if (loc < range.start() || loc >= range.end())
            return false;
    }

    return true;
}

void DiagnosticEngine::issue(const Diagnostic& diagnostic) {
    if (issuedOverLimitErr)
        return;

    const DiagnosticSeverity severity = getSeverity(diagnostic.code, diagnostic.location);
    if (severity == DiagnosticSeverity::Ignored)
        return;

    const bool isError = severity == DiagnosticSeverity::Error ||
                         severity == DiagnosticSeverity::Fatal;
    if (isError && errorLimit && numErrors >= errorLimit) {
        Diagnostic diag(diag::TooManyErrors, SourceLocation::NoLocation);
        issueImpl(diag, DiagnosticSeverity::Fatal);
        issuedOverLimitErr = true;
        return;
    }

    if (!issueImpl(diagnostic, severity))
        return;

    if (severity == DiagnosticSeverity::Warning)
        numWarnings++;
    else if (isError)
        numErrors++;
}

bool DiagnosticEngine::issueImpl(const Diagnostic& diagnostic, DiagnosticSeverity severity) {
    // Walk out until we find a location for this diagnostic that isn't inside a macro.
    SmallVector<SourceLocation, 8> expansionLocs;
    SourceLocation loc = diagnostic.location;
    size_t ignoreExpansionsUntil = 0;
    bool showIncludeStack = false;

    if (loc != SourceLocation::NoLocation) {
        while (sourceManager.isMacroLoc(loc)) {
            SourceLocation prevLoc = loc;
            if (sourceManager.isMacroArgLoc(loc)) {
                expansionLocs.push_back(sourceManager.getExpansionLoc(loc));
                loc = sourceManager.getOriginalLoc(loc);
            }
            else {
                expansionLocs.push_back(loc);
                loc = sourceManager.getExpansionLoc(loc);
            }

            if (checkMacroArgRanges(*this, prevLoc, diagnostic.ranges))
                ignoreExpansionsUntil = expansionLocs.size();
        }

        showIncludeStack = reportedIncludeStack.emplace(loc.buffer()).second;

        auto checkSuppressed = [&](const std::vector<fs::path>& patterns, SourceLocation loc) {
            if (patterns.empty())
                return false;

            auto& path = sourceManager.getFullPath(loc.buffer());
            for (auto& pattern : patterns) {
                if (svGlobMatches(path, pattern))
                    return true;
            }
            return false;
        };

        if (getDefaultSeverity(diagnostic.code) == DiagnosticSeverity::Warning) {
            if (checkSuppressed(ignoreWarnPatterns, loc))
                return false;

            if (ignoreExpansionsUntil < expansionLocs.size() && !ignoreMacroWarnPatterns.empty()) {
                auto originalLoc = sourceManager.getFullyOriginalLoc(
                    expansionLocs[ignoreExpansionsUntil]);

                if (checkSuppressed(ignoreMacroWarnPatterns, originalLoc))
                    return false;
            }
        }
    }

    std::string message = formatMessage(diagnostic);

    ReportedDiagnostic report(diagnostic);
    report.expansionLocs = std::span<SourceLocation>(expansionLocs).subspan(ignoreExpansionsUntil);
    report.ranges = diagnostic.ranges;
    report.location = loc;
    report.severity = severity;
    report.formattedMessage = message;
    report.shouldShowIncludeStack = showIncludeStack;

    for (auto& client : clients)
        client->report(report);

    // Notes are ignored if location is "NoLocation" since they frequently make no
    // sense without location information.
    for (const Diagnostic& note : diagnostic.notes) {
        if (note.location != SourceLocation::NoLocation || note.code.showNoteWithNoLocation())
            issue(note);
    }

    return true;
}

const DiagnosticEngine::FormatterMap& DiagnosticEngine::getFormatters() const {
    if (formatters.empty())
        formatters = defaultFormatters;
    return formatters;
}

std::string DiagnosticEngine::formatMessage(const Diagnostic& diag) const {
    // If we have no arguments, the format string is the entire message.
    if (diag.args.empty())
        return std::string(getMessage(diag.code));

    // Let each formatter have a look at the diagnostic before we begin.
    if (formatters.empty())
        formatters = defaultFormatters;

    for (auto& [key, formatter] : formatters)
        formatter->startMessage(diag);

    // Dynamically build up the list of arguments to pass to the formatting routines.
    fmt::dynamic_format_arg_store<fmt::format_context> args;
    for (auto& arg : diag.args) {
        // Unwrap the argument type (stored as a variant).
        std::visit(
            [&](auto&& t) {
                using T = std::decay_t<decltype(t)>;
                if constexpr (std::is_same_v<Diagnostic::CustomArgType, T>) {
                    args.push_back(formatArg(t));
                }
                else if constexpr (std::is_same_v<ConstantValue, T>) {
                    if (t.isReal())
                        args.push_back(double(t.real()));
                    else if (t.isShortReal())
                        args.push_back(float(t.shortReal()));
                    else
                        args.push_back(t.toString());
                }
                else {
                    args.push_back(t);
                }
            },
            arg);
    }

    return fmt::vformat(getMessage(diag.code), args);
}

std::string DiagnosticEngine::formatArg(const Diagnostic::CustomArgType& arg) const {
    getFormatters();
    if (auto it = formatters.find(arg.first); it != formatters.end())
        return it->second->format(arg.second);

    SLANG_THROW(std::runtime_error("No diagnostic formatter for type"));
}

std::string DiagnosticEngine::formatArg(const Diagnostic::Arg& arg) const {
    return std::visit(
        [&](auto&& t) {
            using T = std::decay_t<decltype(t)>;
            if constexpr (std::is_same_v<Diagnostic::CustomArgType, T>) {
                return formatArg(t);
            }
            else if constexpr (std::is_same_v<ConstantValue, T>) {
                if (t.isReal())
                    return fmt::to_string(double(t.real()));
                else if (t.isShortReal())
                    return fmt::to_string(float(t.shortReal()));
                else
                    return t.toString();
            }
            else {
                return fmt::to_string(t);
            }
        },
        arg);
}

// Walks up a chain of macro argument expansions and collects their buffer IDs.
static void getMacroArgExpansions(const SourceManager& sm, SourceLocation loc, bool isStart,
                                  SmallVectorBase<BufferID>& results) {
    while (sm.isMacroLoc(loc)) {
        if (sm.isMacroArgLoc(loc)) {
            results.push_back(loc.buffer());
            loc = sm.getOriginalLoc(loc);
        }
        else {
            auto range = sm.getExpansionRange(loc);
            loc = isStart ? range.start() : range.end();
        }
    }
}

// Finds all macro argument expansions that are common in both start and end.
static void getCommonMacroArgExpansions(const SourceManager& sm, SourceLocation start,
                                        SourceLocation end, std::vector<BufferID>& results) {
    SmallVector<BufferID> startArgExpansions;
    SmallVector<BufferID> endArgExpansions;
    getMacroArgExpansions(sm, start, true, startArgExpansions);
    getMacroArgExpansions(sm, end, false, endArgExpansions);
    std::ranges::stable_sort(startArgExpansions);
    std::ranges::stable_sort(endArgExpansions);

    std::ranges::set_intersection(startArgExpansions, endArgExpansions,
                                  std::back_inserter(results));
}

// Recursively tries to find an expansion location of `loc` that is in the
// same buffer as `contextLoc`, taking into account macros and macro arguments.
static SourceLocation getMatchingMacroLoc(const SourceManager& sm, SourceLocation loc,
                                          SourceLocation contextLoc, bool isStart,
                                          std::span<const BufferID> commonArgs) {
    if (loc.buffer() == contextLoc.buffer())
        return loc;

    if (!sm.isMacroLoc(loc))
        return {};

    SourceRange macroRange;
    SourceRange macroArgRange;
    if (sm.isMacroArgLoc(loc)) {
        // Only look at the original location of this argument if the other location
        // in the range is also present in the expansion.
        if (std::ranges::binary_search(commonArgs, loc.buffer())) {
            SourceLocation orig = sm.getOriginalLoc(loc);
            macroRange = SourceRange(orig, orig);
        }
        macroArgRange = sm.getExpansionRange(loc);
    }
    else {
        macroRange = sm.getExpansionRange(loc);

        SourceLocation orig = sm.getOriginalLoc(loc);
        macroArgRange = SourceRange(orig, orig);
    }

    SourceLocation macroLoc = isStart ? macroRange.start() : macroRange.end();
    if (macroLoc) {
        macroLoc = getMatchingMacroLoc(sm, macroLoc, contextLoc, isStart, commonArgs);
        if (macroLoc)
            return macroLoc;
    }

    SourceLocation argLoc = isStart ? macroArgRange.start() : macroArgRange.end();
    return getMatchingMacroLoc(sm, argLoc, contextLoc, isStart, commonArgs);
}

void DiagnosticEngine::mapSourceRanges(SourceLocation loc, std::span<const SourceRange> ranges,
                                       SmallVectorBase<SourceRange>& mapped,
                                       bool mapOriginalLocations) const {
    const SourceManager& sm = sourceManager;

    mapped.clear();
    for (auto& range : ranges) {
        SourceLocation start = range.start();
        SourceLocation end = range.end();

        // Find a common parent for start and end. Start with `start` and
        // walk upwards until we find `end`s buffer or run out of expansions.
        SmallMap<BufferID, SourceLocation, 8> startMap;
        while (start.buffer() != end.buffer() && sm.isMacroLoc(start)) {
            startMap[start.buffer()] = start;
            start = sm.getExpansionLoc(start);
        }

        // If `end` wasn't in a direct parent of any of `start`s expansions,
        // repeat the process walking up `end`s expansions.
        if (start.buffer() != end.buffer()) {
            while (sm.isMacroLoc(end) && !startMap.count(end.buffer()))
                end = sm.getExpansionRange(end).end();

            if (sm.isMacroLoc(end))
                start = startMap[end.buffer()];
        }

        // We now have a common macro location; find common argument expansions.
        std::vector<BufferID> commonArgs;
        getCommonMacroArgExpansions(sm, start, end, commonArgs);

        // Backtrack on both start and end until we find a location common with
        // the given context location.
        start = getMatchingMacroLoc(sm, start, loc, true, commonArgs);
        end = getMatchingMacroLoc(sm, end, loc, false, commonArgs);
        if (!start || !end)
            continue;

        // We found common locations, return their actual textual locations.
        if (mapOriginalLocations) {
            start = sm.getFullyOriginalLoc(start);
            end = sm.getFullyOriginalLoc(end);
        }
        mapped.emplace_back(start, end);
    }
}

std::string DiagnosticEngine::reportAll(const SourceManager& sourceManager,
                                        std::span<const Diagnostic> diags) {
    DiagnosticEngine engine(sourceManager);

    auto client = std::make_shared<TextDiagnosticClient>();
    engine.addClient(client);

    for (auto& diag : diags)
        engine.issue(diag);

    return client->getString();
}

Diagnostics DiagnosticEngine::setWarningOptions(std::span<const std::string> options) {
    Diagnostics diags;
    std::vector<std::pair<const DiagGroup*, bool>> groupEnables;
    std::vector<std::pair<DiagCode, bool>> codeEnables;
    flat_hash_map<const DiagGroup*, bool> groupErrors;
    flat_hash_map<DiagCode, bool> codeErrors;
    bool includeDefault = true;

    auto findAndSet = [&](std::string_view name, bool set, const char* errorPrefix,
                          bool isExplicitError) {
        if (auto group = findDiagGroup(name)) {
            if (isExplicitError)
                groupErrors[group] = set;
            else
                groupEnables.emplace_back(group, set);

            // -Werror= also turns on the group.
            if (isExplicitError && set)
                groupEnables.emplace_back(group, true);
        }
        else if (auto codes = findFromOptionName(name); !codes.empty()) {
            for (auto code : codes) {
                if (isExplicitError)
                    codeErrors[code] = set;
                else
                    codeEnables.emplace_back(code, set);

                // -Werror= also turns on the code.
                if (isExplicitError && set)
                    codeEnables.emplace_back(code, true);
            }
        }
        else {
            auto& diag = diags.add(diag::UnknownWarningOption, SourceLocation::NoLocation);
            diag << std::string(errorPrefix) + std::string(name);
        }
    };

    // By default all warnings are turned *on*, and we only want the default set by default,
    // so turn off all warnings here and we'll add the default set at the end.
    setIgnoreAllWarnings(true);

    for (auto& arg : options) {
        if (arg == "everything") {
            // Enable all warnings.
            setIgnoreAllWarnings(false);
        }
        else if (arg == "none") {
            // Disable all warnings.
            includeDefault = false;
            setIgnoreAllWarnings(true);
        }
        else if (arg == "error") {
            setWarningsAsErrors(true);
        }
        else if (arg.starts_with("error=")) {
            findAndSet(arg.substr(6), /* set */ true, "-Werror=", /* isExplicitError */ true);
        }
        else if (arg.starts_with("no-error=")) {
            findAndSet(arg.substr(9), /* set */ false, "-Wno-error=", /* isExplicitError */ true);
        }
        else if (arg.starts_with("no-")) {
            findAndSet(arg.substr(3), /* set */ false, "-Wno-", /* isExplicitError */ false);
        }
        else {
            findAndSet(arg, /* set */ true, "-W", /* isExplicitError */ false);
        }
    }

    auto handleGroup = [&](const DiagGroup* group, bool set) {
        DiagnosticSeverity severity;
        if (!set)
            severity = DiagnosticSeverity::Ignored;
        else if (auto it = groupErrors.find(group); it != groupErrors.end())
            severity = it->second ? DiagnosticSeverity::Error : DiagnosticSeverity::Warning;
        else
            severity = warningsAsErrors ? DiagnosticSeverity::Error : DiagnosticSeverity::Warning;

        for (auto code : group->getDiags())
            severityTable.try_emplace(code, severity);
    };

    // If they didn't pass "none" then enable the default set of warnings.
    if (includeDefault) {
        auto group = findDiagGroup("default"sv);
        SLANG_ASSERT(group);
        handleGroup(group, true);
    }

    // Apply all of the collected settings to the severity table.
    for (auto& [group, set] : groupEnables)
        handleGroup(group, set);

    // Special case for diagnostics with an explicit severity set by API that
    // the user is now trying to downgrade to be not an error.
    for (auto& [code, set] : codeErrors) {
        if (!set) {
            auto it = severityTable.find(code);
            if (it != severityTable.end() && it->second == DiagnosticSeverity::Error)
                it->second = DiagnosticSeverity::Warning;
        }
    }

    for (auto& [code, set] : codeEnables) {
        if (!set) {
            severityTable[code] = DiagnosticSeverity::Ignored;
        }
        else if (auto it = codeErrors.find(code); it != codeErrors.end()) {
            severityTable[code] = it->second ? DiagnosticSeverity::Error
                                             : DiagnosticSeverity::Warning;
        }
        else {
            severityTable[code] = warningsAsErrors ? DiagnosticSeverity::Error
                                                   : DiagnosticSeverity::Warning;
        }
    }

    return diags;
}

template<typename TDirective>
void DiagnosticEngine::setMappingsFromPragmasImpl(BufferID buffer,
                                                  std::span<const TDirective> directives,
                                                  Diagnostics& diags) {

    // Store the state of diagnostics each time the user pushes,
    // and restore the state when they pop.
    std::vector<flat_hash_map<DiagCode, DiagnosticSeverity>> mappingStack;
    mappingStack.emplace_back();

    auto noteDiag = [&](DiagCode code, auto& directive) {
        diagMappings[code][buffer].emplace_back(directive.offset, directive.severity);
        mappingStack.back()[code] = directive.severity;
    };

    for (const SourceManager::DiagnosticDirectiveInfo& directive : directives) {
        auto name = directive.name;
        if (name == "__push__") {
            mappingStack.emplace_back(mappingStack.back());
        }
        else if (name == "__pop__") {
            // If the stack size is 1, push was never called, so just ignore.
            if (mappingStack.size() <= 1)
                continue;

            // Any directives that were set revert to their previous values.
            // If there is no previous value, they go back to the default (unset).
            auto& prev = mappingStack[mappingStack.size() - 2];
            for (auto [code, _] : mappingStack.back()) {
                auto& mappings = diagMappings[code][buffer];
                if (auto it = prev.find(code); it != prev.end())
                    mappings.emplace_back(directive.offset, it->second);
                else
                    mappings.emplace_back(directive.offset, std::nullopt);
            }
            mappingStack.pop_back();
        }
        else {
            if (name.starts_with("-W"sv))
                name = name.substr(2);

            if (auto group = findDiagGroup(name)) {
                for (auto code : group->getDiags())
                    noteDiag(code, directive);
            }
            else if (auto codes = findFromOptionName(name); !codes.empty()) {
                for (auto code : codes)
                    noteDiag(code, directive);
            }
            else {
                auto& diag = diags.add(diag::UnknownWarningOption,
                                       SourceLocation(buffer, directive.offset));
                diag << name;
            }
        }
    }
}

Diagnostics DiagnosticEngine::setMappingsFromPragmas() {
    Diagnostics diags;
    sourceManager.visitDiagnosticDirectives([&](BufferID buffer, auto& directives) {
        setMappingsFromPragmasImpl<SourceManager::DiagnosticDirectiveInfo>(buffer, directives,
                                                                           diags);
    });

    return diags;
}

Diagnostics DiagnosticEngine::setMappingsFromPragmas(BufferID buffer) {
    Diagnostics diags;
    auto directives = sourceManager.getDiagnosticDirectives(buffer);
    if (!directives.empty()) {
        setMappingsFromPragmasImpl<SourceManager::DiagnosticDirectiveInfo>(buffer, directives,
                                                                           diags);
    }

    return diags;
}

std::optional<DiagnosticSeverity> DiagnosticEngine::findMappedSeverity(
    DiagCode code, SourceLocation location) const {
    auto byCode = diagMappings.find(code);
    if (byCode == diagMappings.end())
        return std::nullopt;

    SourceLocation fileLoc = sourceManager.getFullyExpandedLoc(location);
    auto byBuffer = byCode->second.find(fileLoc.buffer());
    if (byBuffer == byCode->second.end())
        return std::nullopt;

    const std::vector<DiagnosticMapping>& mappings = byBuffer->second;
    auto byOffset = std::ranges::lower_bound(mappings, fileLoc.offset(), {},
                                             &DiagnosticMapping::offset);
    if (byOffset == mappings.begin())
        return std::nullopt;

    return (--byOffset)->severity;
}

void DiagnosticEngine::clearIncludeStack() {
    reportedIncludeStack.clear();
}

} // namespace slang
