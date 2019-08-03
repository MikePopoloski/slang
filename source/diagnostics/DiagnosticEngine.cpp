//------------------------------------------------------------------------------
// DiagnosticEngine.h
// Primary interface for managing diagnostic reporting.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticEngine.h"

#include "FmtlibWrapper.h"

#include "slang/diagnostics/DiagnosticClient.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/text/SourceManager.h"
#include "slang/util/StackContainer.h"

namespace slang {

// These are defined in the generated DiagCode.cpp file.
string_view getDefaultMessage(DiagCode code);
DiagnosticSeverity getDefaultSeverity(DiagCode code);
string_view getDefaultOptionName(DiagCode code);
DiagCode findDiagFromOptionName(string_view name);
const DiagGroup* findDefaultDiagGroup(string_view name);

DiagnosticEngine::DiagnosticEngine(const SourceManager& sourceManager) :
    sourceManager(sourceManager) {

    typePrintingOptions = std::make_unique<TypePrintingOptions>();
    typePrintingOptions->addSingleQuotes = true;
    typePrintingOptions->elideScopeNames = true;
    typePrintingOptions->anonymousTypeStyle = TypePrintingOptions::FriendlyName;
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

DiagnosticSeverity DiagnosticEngine::getSeverity(DiagCode code) const {
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

DiagCode DiagnosticEngine::findFromOptionName(string_view optionName) const {
    return findDiagFromOptionName(optionName);
}

const DiagGroup* DiagnosticEngine::findDiagGroup(string_view name) const {
    return findDefaultDiagGroup(name);
}

void DiagnosticEngine::clearMappings() {
    severityTable.clear();
    messageTable.clear();
}

// Checks that all of the given ranges are in the same macro argument expansion as `loc`
static bool checkMacroArgRanges(const DiagnosticEngine& engine, SourceLocation loc,
                                span<const SourceRange> ranges) {
    const SourceManager& sm = engine.getSourceManager();
    if (!sm.isMacroArgLoc(loc))
        return false;

    loc = sm.getExpansionLoc(loc);

    SmallVectorSized<SourceRange, 8> mappedRanges;
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
    DiagnosticSeverity severity = getSeverity(diagnostic.code);
    switch (severity) {
        case DiagnosticSeverity::Ignored:
            return;
        case DiagnosticSeverity::Note:
            break;
        case DiagnosticSeverity::Warning:
            numWarnings++;
            break;
        case DiagnosticSeverity::Error:
        case DiagnosticSeverity::Fatal:
            if (errorLimit && numErrors >= errorLimit)
                return;

            numErrors++;
            break;
    }

    // Walk out until we find a location for this diagnostic that isn't inside a macro.
    SmallVectorSized<SourceLocation, 8> expansionLocs;
    SourceLocation loc = diagnostic.location;
    size_t ignoreUntil = 0;

    while (sourceManager.isMacroLoc(loc)) {
        SourceLocation prevLoc = loc;
        if (sourceManager.isMacroArgLoc(loc)) {
            expansionLocs.append(sourceManager.getExpansionLoc(loc));
            loc = sourceManager.getOriginalLoc(loc);
        }
        else {
            expansionLocs.append(loc);
            loc = sourceManager.getExpansionLoc(loc);
        }

        if (checkMacroArgRanges(*this, prevLoc, diagnostic.ranges))
            ignoreUntil = expansionLocs.size();
    }

    // Keep track of whether we should show the include stack for this diagnostic.
    bool showIncludeStack = reportedIncludeStack.emplace(loc.buffer()).second;

    std::string message = formatMessage(diagnostic);

    ReportedDiagnostic report(diagnostic);
    report.expansionLocs = make_span(expansionLocs).subspan(ptrdiff_t(ignoreUntil));
    report.ranges = diagnostic.ranges;
    report.location = loc;
    report.severity = severity;
    report.formattedMessage = message;
    report.shouldShowIncludeStack = showIncludeStack;

    for (auto& client : clients)
        client->report(report);

    for (const Diagnostic& note : diagnostic.notes)
        issue(note);
}

std::string DiagnosticEngine::formatMessage(const Diagnostic& diag) const {
    // If we have no arguments, the format string is the entire message.
    if (diag.args.empty())
        return std::string(getMessage(diag.code));

    // For formatting types we want to know the full set of all types we'll be
    // including in the message (to see if we need to disambiguate them) so keep
    // track of them while building the arugment list.
    SmallVectorSized<const Type*, 8> allTypes;

    // Dynamically build up the list of arguments to pass to the formatting routines.
    using ctx = format::detail::FormatContext;
    std::vector<fmt::basic_format_arg<ctx>> args;
    for (auto& arg : diag.args) {
        // Unwrap the argument type (stored as a variant).
        std::visit(
            [&](auto&& t) {
                // If the argument is a pointer, the fmtlib API needs it unwrapped into a reference.
                using T = std::decay_t<decltype(t)>;
                if constexpr (std::is_pointer_v<T>)
                    args.push_back(fmt::internal::make_arg<ctx>(*t));
                else
                    args.push_back(fmt::internal::make_arg<ctx>(t));

                if constexpr (std::is_same_v<T, const Type*>)
                    allTypes.append(t);
            },
            arg);
    }

    using Range = fmt::back_insert_range<fmt::internal::basic_buffer<char>>;

    auto&& formatStr = fmt::to_string_view(getMessage(diag.code));
    fmt::memory_buffer out;
    fmt::format_handler<format::detail::ArgFormatter<Range>, char, ctx> handler(
        out, formatStr, fmt::basic_format_args(args.data(), (unsigned)args.size()),
        fmt::internal::locale_ref());

    typePrintingOptions->disambiguateTypes = allTypes;
    handler.context.typeOptions = typePrintingOptions.get();

    fmt::internal::parse_format_string<false>(formatStr, handler);

    return std::string(out.data(), out.size());
}

// Walks up a chain of macro argument expansions and collects their buffer IDs.
static void getMacroArgExpansions(const SourceManager& sm, SourceLocation loc, bool isStart,
                                  SmallVector<BufferID>& results) {
    while (sm.isMacroLoc(loc)) {
        if (sm.isMacroArgLoc(loc)) {
            results.append(loc.buffer());
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
    SmallVectorSized<BufferID, 8> startArgExpansions;
    SmallVectorSized<BufferID, 8> endArgExpansions;
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
                                       SmallVector<SourceRange>& mapped,
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
        mapped.emplace(start, end);
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

} // namespace slang
