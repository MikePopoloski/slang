//------------------------------------------------------------------------------
// JsonDiagnosticClient.cpp
// Diagnostic client that formats to JSON
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/JsonDiagnosticClient.h"

#include <fmt/format.h>

#include "slang/text/Json.h"
#include "slang/text/SourceManager.h"

namespace slang {

void JsonDiagnosticClient::report(const ReportedDiagnostic& diag) {
    writer.startObject();
    writer.writeProperty("severity");
    writer.writeValue(getSeverityString(diag.severity));
    writer.writeProperty("message");
    writer.writeValue(diag.formattedMessage);

    auto optionName = engine->getOptionName(diag.originalDiagnostic.code);
    if (!optionName.empty()) {
        writer.writeProperty("optionName");
        writer.writeValue(optionName);
    }

    if (diag.location.buffer() != SourceLocation::NoLocation.buffer()) {
        auto loc = diag.location;
        writer.writeProperty("location");
        writer.writeValue(fmt::format("{}:{}:{}", sourceManager->getFileName(loc),
                                      sourceManager->getLineNumber(loc),
                                      sourceManager->getColumnNumber(loc)));
    }

    if (diag.shouldShowIncludeStack) {
        SmallVector<SourceLocation> includeStack;
        getIncludeStack(diag.location.buffer(), includeStack);

        if (!includeStack.empty()) {
            writer.writeProperty("includeStack");
            writer.startArray();
            for (int i = int(includeStack.size()) - 1; i >= 0; i--) {
                SourceLocation loc = includeStack[size_t(i)];
                writer.writeValue(fmt::format("{}:{}", sourceManager->getFileName(loc),
                                              sourceManager->getLineNumber(loc)));
            }
            writer.endArray();
        }
    }

    // Print out the hierarchy where the diagnostic occurred, if we know it.
    auto& od = diag.originalDiagnostic;
    auto& symbolPathCB = engine->getSymbolPathCB();
    if (od.symbol && symbolPathCB) {
        writer.writeProperty("symbolPath");
        writer.writeValue(symbolPathCB(*od.symbol));
    }

    // Write out macro expansions, if we have any, in reverse order.
    if (!diag.expansionLocs.empty()) {
        writer.writeProperty("macroStack");
        writer.startArray();
        for (auto it = diag.expansionLocs.rbegin(); it != diag.expansionLocs.rend(); it++) {
            writer.startObject();
            writer.writeProperty("name");

            SourceLocation loc = *it;
            writer.writeValue(sourceManager->getMacroName(loc));

            loc = sourceManager->getFullyOriginalLoc(loc);
            if (loc.buffer() != SourceLocation::NoLocation.buffer()) {
                writer.writeProperty("location");
                writer.writeValue(fmt::format("{}:{}:{}", sourceManager->getFileName(loc),
                                              sourceManager->getLineNumber(loc),
                                              sourceManager->getColumnNumber(loc)));
            }

            writer.endObject();
        }
        writer.endArray();
    }
    writer.endObject();
}

} // namespace slang
