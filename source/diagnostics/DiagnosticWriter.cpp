//------------------------------------------------------------------------------
// DiagnosticWriter.h
// Diagnostic rendering.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticWriter.h"

#include <fmt/ostream.h>

#include "slang/text/FormatBuffer.h"
#include "slang/text/SourceManager.h"
#include "slang/util/StackContainer.h"

namespace slang {

// These are defined in the generated DiagCode.cpp file.
string_view getMessage(DiagCode code);
DiagnosticSeverity getSeverity(DiagCode code);

static const char* severityToString[] = { "note", "warning", "error" };

DiagnosticWriter::DiagnosticWriter(const SourceManager& sourceManager) :
    sourceManager(sourceManager) {
}

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

static void mapDiagnosticRanges(const SourceManager& sm, SourceLocation loc,
                                span<const SourceRange> ranges, SmallVector<SourceRange>& mapped) {
    for (auto& range : ranges) {
        SourceLocation start = range.start();
        SourceLocation end = range.end();

        SmallMap<BufferID, SourceLocation, 8> startMap;
        while (sm.isMacroLoc(start) && start.buffer() != end.buffer()) {
            startMap[start.buffer()] = start;
            start = sm.getExpansionLoc(start);
        }

        if (start.buffer() != end.buffer()) {
            while (sm.isMacroLoc(end) && !startMap.count(end.buffer()))
                end = sm.getExpansionRange(end).end();

            if (sm.isMacroLoc(end))
                start = startMap[end.buffer()];
        }

        // We now have a common macro location; find common argument expansions.
        std::vector<BufferID> commonArgs;
        getCommonMacroArgExpansions(sm, start, end, commonArgs);

        start = getMatchingMacroLoc(sm, start, loc, true, commonArgs);
        end = getMatchingMacroLoc(sm, end, loc, false, commonArgs);
        if (!start || !end)
            continue;

        start = sm.getFullyOriginalLoc(start);
        end = sm.getFullyOriginalLoc(end);
        mapped.emplace(start, end);
    }
}

static bool checkMacroArgRanges(const SourceManager& sm, SourceLocation loc,
                                span<const SourceRange> ranges) {
    if (!sm.isMacroArgLoc(loc))
        return false;

    SmallVectorSized<SourceRange, 8> mappedRanges;
    mapDiagnosticRanges(sm, loc, ranges, mappedRanges);

    if (ranges.size() > mappedRanges.size())
        return false;

    loc = sm.getExpansionLoc(loc);

    for (auto& range : mappedRanges) {
        if (!sm.isMacroArgLoc(range.start()) || !sm.isMacroArgLoc(range.end()))
            return false;

        if (sm.getExpansionLoc(range.start()) != loc || sm.getExpansionLoc(range.end()) != loc)
            return false;
    }

    return true;
}

std::string DiagnosticWriter::report(const Diagnostic& diagnostic) {
    // walk out until we find a location for this diagnostic that isn't inside a macro
    SmallVectorSized<SourceLocation, 8> expansionLocs;
    SourceLocation location = diagnostic.location;
    size_t ignoreUntil = 0;

    while (sourceManager.isMacroLoc(location)) {
        SourceLocation prevLoc = location;
        if (sourceManager.isMacroArgLoc(location)) {
            expansionLocs.append(sourceManager.getExpansionLoc(location));
            location = sourceManager.getOriginalLoc(location);
        }
        else {
            expansionLocs.append(location);
            location = sourceManager.getExpansionLoc(location);
        }

        if (checkMacroArgRanges(sourceManager, prevLoc, diagnostic.ranges))
            ignoreUntil = expansionLocs.size();
    }

    // build the error message from arguments, if we have any
    FormatBuffer buffer;
    string_view format = getMessage(diagnostic.code);
    DiagnosticSeverity severity = getSeverity(diagnostic.code);
    std::string message;

    if (diagnostic.args.empty()) {
        message = format;
    }
    else {
        // The fmtlib API for arg lists isn't very pretty, but it gets the job done
        using ctx = fmt::format_context;
        std::vector<fmt::basic_format_arg<ctx>> args;
        for (auto& arg : diagnostic.args)
            args.push_back(fmt::internal::make_arg<ctx>(arg));

        message =
            fmt::vformat(format, fmt::basic_format_args<ctx>(args.data(), (unsigned)args.size()));
    }

    SmallVectorSized<SourceRange, 8> mappedRanges;
    mapDiagnosticRanges(sourceManager, location, diagnostic.ranges, mappedRanges);
    formatDiag(buffer, location, mappedRanges, severityToString[(int)severity], message);

    // write out macro expansions, if we have any
    size_t index = 0;
    while (!expansionLocs.empty()) {
        location = expansionLocs.back();
        expansionLocs.pop();
        index++;

        if (index <= ignoreUntil)
            continue;

        std::string name{ sourceManager.getMacroName(location) };
        if (name.empty())
            name = "expanded from here";
        else
            name = "expanded from macro '" + name + "'";

        SmallVectorSized<SourceRange, 8> macroRanges;
        mapDiagnosticRanges(sourceManager, location, diagnostic.ranges, macroRanges);
        formatDiag(buffer, sourceManager.getFullyOriginalLoc(location), macroRanges, "note", name);
    }

    for (const Diagnostic& note : diagnostic.notes)
        buffer.append(report(note));

    return buffer.str();
}

std::string DiagnosticWriter::report(const Diagnostics& diagnostics) {
    std::deque<SourceLocation> includeStack;
    BufferID lastBuffer;
    FormatBuffer buffer;

    for (auto& diag : diagnostics) {
        SourceLocation loc = sourceManager.getFullyExpandedLoc(diag.location);
        if (loc.buffer() != lastBuffer) {
            // We're looking at diagnostics from another file now. See if we should print
            // include stack info before we go on with the reports.
            lastBuffer = loc.buffer();
            getIncludeStack(lastBuffer, includeStack);

            for (auto& includeLoc : includeStack) {
                buffer.format("in file included from {}:{}:\n",
                              sourceManager.getFileName(includeLoc),
                              sourceManager.getLineNumber(includeLoc));
            }
        }
        buffer.append(report(diag));
    }
    return buffer.str();
}

string_view DiagnosticWriter::getBufferLine(SourceLocation location, uint32_t col) {
    string_view text = sourceManager.getSourceText(location.buffer());
    if (text.empty())
        return "";

    const char* start = text.data() + location.offset() - (col - 1);
    const char* curr = start;
    while (*curr != '\n' && *curr != '\r' && *curr != '\0')
        curr++;

    return string_view(start, (uint32_t)(curr - start));
}

void DiagnosticWriter::getIncludeStack(BufferID buffer, std::deque<SourceLocation>& stack) {
    stack.clear();
    while (buffer) {
        SourceLocation loc = sourceManager.getIncludedFrom(buffer);
        if (!loc.buffer())
            break;

        stack.push_front(loc);
        buffer = loc.buffer();
    }
}

void DiagnosticWriter::highlightRange(SourceRange range, SourceLocation caretLoc, uint32_t col,
                                      string_view sourceLine, std::string& buffer) {
    // Trim the range so that it only falls on the same line as the cursor
    uint32_t start = range.start().offset();
    uint32_t end = range.end().offset();
    uint32_t startOfLine = caretLoc.offset() - (col - 1);
    uint32_t endOfLine = startOfLine + (uint32_t)sourceLine.length();
    if (start < startOfLine)
        start = startOfLine;
    if (end > endOfLine)
        end = endOfLine;

    if (start >= end)
        return;

    // walk the range in to skip any leading or trailing whitespace
    start -= startOfLine;
    end -= startOfLine;
    while (sourceLine[start] == ' ' || sourceLine[start] == '\t') {
        start++;
        if (start == end)
            return;
    }
    while (sourceLine[end - 1] == ' ' || sourceLine[end - 1] == '\t') {
        end--;
        if (start == end)
            return;
    }

    // finally add the highlight chars
    for (; start != end; start++)
        buffer[start] = '~';
}

template<typename T>
void DiagnosticWriter::formatDiag(T& buffer, SourceLocation loc, span<const SourceRange> ranges,
                                  const char* severity, const std::string& msg) {
    uint32_t col = sourceManager.getColumnNumber(loc);
    buffer.format("{}:{}:{}: {}: {}", sourceManager.getFileName(loc),
                  sourceManager.getLineNumber(loc), col, severity, msg);

    string_view line = getBufferLine(loc, col);
    if (!line.empty()) {
        buffer.format("\n{}\n", line);

        // Highlight any ranges and print the caret location.
        std::string highlight(std::max(line.length(), (size_t)col), ' ');

        // handle tabs to get proper alignment on a terminal
        for (uint32_t i = 0; i < line.length(); ++i) {
            if (line[i] == '\t')
                highlight[i] = '\t';
        }

        for (SourceRange range : ranges)
            highlightRange(range, loc, col, line, highlight);

        highlight[col - 1] = '^';
        highlight.erase(highlight.find_last_not_of(' ') + 1);
        buffer.append(highlight);
    }
    buffer.append("\n");
}

} // namespace slang
