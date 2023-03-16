//------------------------------------------------------------------------------
// DiagnosticEngine.cpp
// Primary interface for managing diagnostic reporting
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticEngine.h"

#include <fmt/args.h>

#include "slang/diagnostics/DiagArgFormatter.h"
#include "slang/diagnostics/DiagnosticClient.h"
#include "slang/diagnostics/MetaDiags.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/text/SourceManager.h"
#include "slang/util/StackContainer.h"
#include "slang/util/String.h"

namespace slang {

// These are defined in the generated DiagCode.cpp file.
string_view getDefaultMessage(DiagCode code);
DiagnosticSeverity getDefaultSeverity(DiagCode code);
string_view getDefaultOptionName(DiagCode code);
span<const DiagCode> findDiagsFromOptionName(string_view name);
const DiagGroup* findDefaultDiagGroup(string_view name);

DiagnosticEngine::FormatterMap DiagnosticEngine::defaultFormatters;

DiagnosticEngine::DiagnosticEngine(const SourceManager& sourceManager) :
    sourceManager(sourceManager), formatters(defaultFormatters) {
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

void DiagnosticEngine::setSeverity(const DiagGroup& group, DiagnosticSeverity severity) {
    for (auto diag : group.getDiags())
        setSeverity(diag, severity);
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

string_view DiagnosticEngine::getMessage(DiagCode code) const {
    if (auto it = messageTable.find(code); it != messageTable.end())
        return it->second;
    return getDefaultMessage(code);
}

string_view DiagnosticEngine::getOptionName(DiagCode code) const {
    return getDefaultOptionName(code);
}

span<const DiagCode> DiagnosticEngine::findFromOptionName(string_view optionName) const {
    return findDiagsFromOptionName(optionName);
}

const DiagGroup* DiagnosticEngine::findDiagGroup(string_view name) const {
    return findDefaultDiagGroup(name);
}

void DiagnosticEngine::clearMappings() {
    severityTable.clear();
    messageTable.clear();
}

void DiagnosticEngine::clearMappings(DiagnosticSeverity severity) {
    for (auto it = severityTable.begin(); it != severityTable.end();) {
        if (it->second == severity)
            it = severityTable.erase(it);
        else
            it++;
    }
}

void DiagnosticEngine::addIgnorePath(const std::filesystem::path& path) {
    ignoreWarnPrefixes.emplace_back(path);
}

// Checks that all of the given ranges are in the same macro argument expansion as `loc`
static bool checkMacroArgRanges(const DiagnosticEngine& engine, SourceLocation loc,
                                span<const SourceRange> ranges) {
    const SourceManager& sm = engine.getSourceManager();
    if (!sm.isMacroArgLoc(loc))
        return false;

    loc = sm.getExpansionLoc(loc);

    SmallVector<SourceRange, 8> mappedRanges;
    engine.mapSourceRanges(loc, ranges, mappedRanges, false);

    if (ranges.size() > mappedRanges.size())
        return false;

    for (auto& range : mappedRanges) {
        ASSERT(range.start().buffer() == loc.buffer());
        ASSERT(range.end().buffer() == loc.buffer());

        if (loc < range.start() || loc >= range.end())
            return false;
    }

    return true;
}

void DiagnosticEngine::issue(const Diagnostic& diagnostic) {
    if (issuedOverLimitErr)
        return;

    DiagnosticSeverity severity = getSeverity(diagnostic.code, diagnostic.location);
    switch (severity) {
        case DiagnosticSeverity::Ignored:
            return;
        case DiagnosticSeverity::Note:
        case DiagnosticSeverity::Warning:
            break;
        case DiagnosticSeverity::Error:
        case DiagnosticSeverity::Fatal:
            if (errorLimit && numErrors >= errorLimit) {
                Diagnostic diag(diag::TooManyErrors, SourceLocation::NoLocation);
                issueImpl(diag, DiagnosticSeverity::Fatal);
                issuedOverLimitErr = true;
                return;
            }

            numErrors++;
            break;
    }

    if (!issueImpl(diagnostic, severity))
        return;

    if (severity == DiagnosticSeverity::Warning)
        numWarnings++;
}

bool DiagnosticEngine::issueImpl(const Diagnostic& diagnostic, DiagnosticSeverity severity) {
    // Walk out until we find a location for this diagnostic that isn't inside a macro.
    SmallVector<SourceLocation, 8> expansionLocs;
    SourceLocation loc = diagnostic.location;
    size_t ignoreUntil = 0;
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
                ignoreUntil = expansionLocs.size();
        }

        showIncludeStack = reportedIncludeStack.emplace(loc.buffer()).second;

        if (!ignoreWarnPrefixes.empty() &&
            getDefaultSeverity(diagnostic.code) == DiagnosticSeverity::Warning) {

            auto& path = sourceManager.getFullPath(loc.buffer());
            for (auto& prefix : ignoreWarnPrefixes) {
                auto [_, mismatchIt] = std::mismatch(path.begin(), path.end(), prefix.begin(),
                                                     prefix.end());
                if (mismatchIt == prefix.end())
                    return false;
            }
        }
    }

    std::string message = formatMessage(diagnostic);

    ReportedDiagnostic report(diagnostic);
    report.expansionLocs = span<SourceLocation>(expansionLocs).subspan(ignoreUntil);
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
        if (note.location != SourceLocation::NoLocation || note.code == diag::NoteFromHere2)
            issue(note);
    }

    return true;
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
                // If the argument is a pointer, the fmtlib API needs it unwrapped into a reference.
                using T = std::decay_t<decltype(t)>;
                if constexpr (std::is_same_v<std::any, T>) {
                    if (auto it = formatters.find(t.type()); it != formatters.end())
                        args.push_back(it->second->format(t));
                    else
                        throw std::runtime_error("No diagnostic formatter for type");
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
    std::stable_sort(startArgExpansions.begin(), startArgExpansions.end());
    std::stable_sort(endArgExpansions.begin(), endArgExpansions.end());

    std::set_intersection(startArgExpansions.begin(), startArgExpansions.end(),
                          endArgExpansions.begin(), endArgExpansions.end(),
                          std::back_inserter(results));
}

// Recursively tries to find an expansion location of `loc` that is in the
// same buffer as `contextLoc`, taking into account macros and macro arguments.
static SourceLocation getMatchingMacroLoc(const SourceManager& sm, SourceLocation loc,
                                          SourceLocation contextLoc, bool isStart,
                                          span<const BufferID> commonArgs) {
    if (loc.buffer() == contextLoc.buffer())
        return loc;

    if (!sm.isMacroLoc(loc))
        return {};

    SourceRange macroRange;
    SourceRange macroArgRange;
    if (sm.isMacroArgLoc(loc)) {
        // Only look at the original location of this argument if the other location
        // in the range is also present in the expansion.
        if (std::binary_search(commonArgs.begin(), commonArgs.end(), loc.buffer())) {
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

void DiagnosticEngine::mapSourceRanges(SourceLocation loc, span<const SourceRange> ranges,
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
        while (sm.isMacroLoc(start) && start.buffer() != end.buffer()) {
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
                                        span<const Diagnostic> diags) {
    DiagnosticEngine engine(sourceManager);

    auto client = std::make_shared<TextDiagnosticClient>();
    engine.addClient(client);

    for (auto& diag : diags)
        engine.issue(diag);

    return client->getString();
}

void DiagnosticEngine::setDefaultWarnings() {
    setIgnoreAllWarnings(true);
    setSeverity(*findDiagGroup("default"sv), DiagnosticSeverity::Warning);
}

Diagnostics DiagnosticEngine::setWarningOptions(span<const std::string> options) {
    Diagnostics diags;
    auto findAndSet = [&](string_view name, DiagnosticSeverity severity, const char* errorPrefix) {
        if (auto group = findDiagGroup(name)) {
            setSeverity(*group, severity);
        }
        else if (auto codes = findFromOptionName(name); !codes.empty()) {
            for (auto code : codes)
                setSeverity(code, severity);
        }
        else {
            auto& diag = diags.add(diag::UnknownWarningOption, SourceLocation::NoLocation);
            diag << std::string(errorPrefix) + std::string(name);
        }
    };

    for (auto& arg : options) {
        if (arg == "everything") {
            // Enable all warnings.
            clearMappings(DiagnosticSeverity::Ignored);
            setIgnoreAllWarnings(false);
        }
        else if (arg == "none") {
            // Disable all warnings.
            clearMappings(DiagnosticSeverity::Warning);
            setIgnoreAllWarnings(true);
        }
        else if (arg == "error") {
            for (auto it = severityTable.begin(); it != severityTable.end(); it++) {
                if (it->second == DiagnosticSeverity::Warning)
                    it->second = DiagnosticSeverity::Error;
            }
            setWarningsAsErrors(true);
        }
        else if (startsWith(arg, "error=")) {
            findAndSet(arg.substr(6), DiagnosticSeverity::Error, "-Werror=");
        }
        else if (startsWith(arg, "no-error=")) {
            findAndSet(arg.substr(9), DiagnosticSeverity::Warning, "-Wno-error=");
        }
        else if (startsWith(arg, "no-")) {
            findAndSet(arg.substr(3), DiagnosticSeverity::Ignored, "-Wno-");
        }
        else {
            findAndSet(arg, DiagnosticSeverity::Warning, "-W");
        }
    }

    return diags;
}

template<typename TDirective>
void DiagnosticEngine::setMappingsFromPragmasImpl(BufferID buffer,
                                                  span<const TDirective> directives,
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
            if (startsWith(name, "-W"sv))
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
    auto byOffset = std::lower_bound(mappings.begin(), mappings.end(), fileLoc.offset(),
                                     [](const DiagnosticMapping& mapping, size_t off) {
                                         return mapping.offset < off;
                                     });

    if (byOffset == mappings.begin())
        return std::nullopt;

    return (--byOffset)->severity;
}

} // namespace slang
