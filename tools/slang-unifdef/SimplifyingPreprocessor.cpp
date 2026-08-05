//------------------------------------------------------------------------------
// SimplifyingPreprocessor.cpp
// Redaction of `ifdef / `ifndef conditional blocks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "SimplifyingPreprocessor.h"

#include "fmt/format.h"
#include <optional>
#include <string_view>
#include <vector>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/Lexer.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/text/CharInfo.h"
#include "slang/text/SourceLocation.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/Util.h"

using namespace slang;
using namespace slang::parsing;
using namespace slang::syntax;

namespace {

enum class DirectiveKind { IfDef, IfNDef, ElsIf, Else, EndIf };

struct Directive {
    DirectiveKind kind;
    size_t start;
    size_t end;
    size_t tokenEnd;
    std::optional<std::string_view> macroName;
};

struct Branch {
    Directive directive;
    std::string content;
};

struct Frame {
    std::vector<Branch> branches;
    bool sawElse = false;
};

struct TokenCursor {
    Lexer& lexer;
    std::optional<Token> lookahead;

    Token peek() {
        if (!lookahead)
            lookahead = lexer.lex();
        return *lookahead;
    }

    Token consume() {
        if (lookahead) {
            auto token = *lookahead;
            lookahead.reset();
            return token;
        }

        return lexer.lex();
    }
};

// Map slang's directive syntax kinds to the small subset this tool simplifies.
std::optional<DirectiveKind> getDirectiveKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::IfDefDirective:
            return DirectiveKind::IfDef;
        case SyntaxKind::IfNDefDirective:
            return DirectiveKind::IfNDef;
        case SyntaxKind::ElsIfDirective:
            return DirectiveKind::ElsIf;
        case SyntaxKind::ElseDirective:
            return DirectiveKind::Else;
        case SyntaxKind::EndIfDirective:
            return DirectiveKind::EndIf;
        default:
            return std::nullopt;
    }
}

// Return the byte offset of a token in the original source buffer.
size_t getOffset(Token token) {
    return size_t(token.location().offset());
}

// Return the offset just past the current physical source line.
size_t getLineEnd(std::string_view text, size_t offset) {
    while (offset < text.size()) {
        char c = text[offset++];
        if (!isNewline(c))
            continue;

        // Treat a CRLF (or LFCR) pair as one newline sequence.
        if (offset < text.size() && isNewline(text[offset]) && text[offset] != c)
            offset++;
        break;
    }
    return offset;
}

// Return the newline sequence immediately before offset, if any.
std::string_view getLineEnding(std::string_view text, size_t offset) {
    if (offset == 0 || !isNewline(text[offset - 1]))
        return {};

    size_t start = offset - 1;
    if (start > 0 && isNewline(text[start - 1]) && text[start - 1] != text[start])
        start--;
    return text.substr(start, offset - start);
}

// Return the byte offset just past a token's raw source text.
size_t getTokenEnd(Token token) {
    return getOffset(token) + token.rawText().size();
}

// Return true if only whitespace precedes offset on its source line.
bool tokenStartsLine(std::string_view text, size_t offset) {
    while (offset > 0 && !isNewline(text[offset - 1])) {
        offset--;
        if (!isWhitespace(text[offset]))
            return false;
    }
    return true;
}

// Return true for directive forms that can carry a simple macro name condition.
bool hasConditionMacro(DirectiveKind kind) {
    return kind == DirectiveKind::IfDef || kind == DirectiveKind::IfNDef ||
           kind == DirectiveKind::ElsIf;
}

// Read the full directive span and optional simple macro name from the token stream.
Directive readDirective(Token directiveToken, TokenCursor& tokens, std::string_view text) {
    auto kind = getDirectiveKind(directiveToken.directiveKind());
    SLANG_ASSERT(kind);

    // The redactor removes the directive token and, for conditionals with a macro name,
    // the first identifier token that follows it. If the directive is alone on its
    // physical line, also consume the line ending so multiline conditionals don't leave
    // behind blank lines. If source follows on the same line, stop at the directive
    // syntax and let that source be emitted or skipped as branch contents.
    Directive directive{*kind, getOffset(directiveToken), 0, getTokenEnd(directiveToken),
                        std::nullopt};

    Token lastDirectiveToken = directiveToken;
    Token nextToken = tokens.peek();
    if (hasConditionMacro(*kind)) {
        if (nextToken.kind != TokenKind::EndOfFile && nextToken.isOnSameLine() &&
            nextToken.kind == TokenKind::Identifier) {
            directive.macroName = nextToken.valueText();
            lastDirectiveToken = tokens.consume();
            nextToken = tokens.peek();
        }
    }

    bool endsLine = nextToken.kind == TokenKind::EndOfFile || !nextToken.isOnSameLine();

    directive.end = getTokenEnd(lastDirectiveToken);
    if (endsLine && tokenStartsLine(text, directive.start))
        directive.end = getLineEnd(text, directive.end);

    return directive;
}

// Return a forced branch value when the directive is controlled by a configured macro.
std::optional<bool> getForcedConditionValue(const Directive& directive,
                                            const flat_hash_map<std::string, bool>& macroValues) {
    if (!directive.macroName)
        return std::nullopt;

    auto it = macroValues.find(std::string(*directive.macroName));
    if (it == macroValues.end())
        return std::nullopt;

    bool result = it->second;
    if (directive.kind == DirectiveKind::IfNDef)
        result = !result;
    return result;
}

// Return the exact original source text covered by the directive span.
std::string_view getDirectiveText(std::string_view text, const Directive& directive) {
    return text.substr(directive.start, directive.end - directive.start);
}

// Return the original condition text after an `elsif token, including spacing.
std::string_view getElsIfConditionText(std::string_view text, const Directive& directive) {
    return text.substr(directive.tokenEnd, directive.end - directive.tokenEnd);
}

// Render the first preserved branch, converting a leading `elsif into `ifdef.
std::string getFirstBranchDirectiveText(std::string_view text, const Directive& directive) {
    if (directive.kind != DirectiveKind::ElsIf)
        return std::string(getDirectiveText(text, directive));

    std::string result(LexerFacts::getDirectiveText(SyntaxKind::IfDefDirective));
    result.append(getElsIfConditionText(text, directive));
    return result;
}

// Render an artificial `else that matches the original directive's line shape.
std::string getElseDirectiveText(std::string_view text, const Directive& directive) {
    std::string result(LexerFacts::getDirectiveText(SyntaxKind::ElseDirective));
    result.append(getLineEnding(text, directive.end));
    return result;
}

// Report an unsupported conditional structure as a user-facing redaction error.
[[noreturn]] void throwError(std::string_view message) {
    SLANG_THROW(RedactionError(fmt::format("cannot redact: {}", message)));
}

// Append the branch content that survived simplification, trimming only whitespace
// that belonged to removed same-line directive scaffolding.
void appendSelectedBranchContent(std::string& output, std::string_view text, const Branch& branch,
                                 bool frameStartsLine) {
    std::string_view content = branch.content;

    if (frameStartsLine && branch.directive.end > 0 && !isNewline(text[branch.directive.end - 1])) {
        while (!content.empty() && isTabOrSpace(content.front()))
            content.remove_prefix(1);
    }

    while (!content.empty() && isTabOrSpace(content.back()))
        content.remove_suffix(1);

    output.append(content);
}

// Simplify a completed conditional frame using forced macro values.
//
// Unknown branches are preserved as a residual conditional. Forced-false branches before
// the first unknown branch are removed, and a later forced-true branch becomes the
// residual `else body because all following branches are unreachable.
std::string renderFrame(Frame&& frame, const Directive& endDirective, std::string_view text,
                        const flat_hash_map<std::string, bool>& macroValues) {
    std::string result;
    bool frameStartsLine = tokenStartsLine(text, frame.branches.front().directive.start);

    std::vector<size_t> keptBranches;
    std::optional<size_t> selectedBranch;
    std::optional<size_t> elseBranch;
    for (size_t branchIndex = 0; branchIndex < frame.branches.size(); branchIndex++) {
        const auto& branchDirective = frame.branches[branchIndex].directive;
        if (branchDirective.kind == DirectiveKind::Else) {
            elseBranch = branchIndex;
            break;
        }

        auto value = getForcedConditionValue(branchDirective, macroValues);
        if (!value)
            keptBranches.push_back(branchIndex);
        else if (*value) {
            selectedBranch = branchIndex;
            break;
        }
    }

    if (keptBranches.empty()) {
        if (selectedBranch)
            appendSelectedBranchContent(result, text, frame.branches[*selectedBranch],
                                        frameStartsLine);
        else if (elseBranch)
            appendSelectedBranchContent(result, text, frame.branches[*elseBranch], frameStartsLine);
        return result;
    }

    for (size_t keptIndex = 0; keptIndex < keptBranches.size(); keptIndex++) {
        const auto& branch = frame.branches[keptBranches[keptIndex]];
        if (keptIndex == 0)
            result.append(getFirstBranchDirectiveText(text, branch.directive));
        else
            result.append(getDirectiveText(text, branch.directive));

        result.append(branch.content);
    }

    if (selectedBranch) {
        const auto& branch = frame.branches[*selectedBranch];
        result.append(getElseDirectiveText(text, branch.directive));
        appendSelectedBranchContent(result, text, branch, frameStartsLine);
    }
    else if (elseBranch) {
        const auto& branch = frame.branches[*elseBranch];
        result.append(getDirectiveText(text, branch.directive));
        result.append(branch.content);
    }

    result.append(getDirectiveText(text, endDirective));
    return result;
}

} // namespace

// Walk the source once with the lexer, maintaining a stack of open conditionals.
// Completed nested frames render back into their parent branch contents.
SimplifyingPreprocessor& SimplifyingPreprocessor::redact(SourceBuffer buffer) {
    auto sourceText = buffer.data;
    if (!sourceText.empty() && sourceText.back() == '\0')
        sourceText.remove_suffix(1);

    BumpAllocator alloc;
    Diagnostics diagnostics;
    Lexer lexer(buffer, alloc, diagnostics, sourceManager);

    TokenCursor tokens{lexer};
    std::vector<Frame> frames;
    size_t cursor = 0;

    auto appendText = [&](std::string_view text) {
        if (frames.empty())
            output.append(text);
        else
            frames.back().branches.back().content.append(text);
    };

    while (true) {
        auto token = tokens.consume();
        if (token.kind == TokenKind::EndOfFile)
            break;

        if (token.kind != TokenKind::Directive || !getDirectiveKind(token.directiveKind()))
            continue;

        auto directive = readDirective(token, tokens, sourceText);
        appendText(sourceText.substr(cursor, directive.start - cursor));

        switch (directive.kind) {
            case DirectiveKind::IfDef:
            case DirectiveKind::IfNDef: {
                Frame frame;
                frame.branches.push_back({directive, {}});
                frames.push_back(std::move(frame));
                break;
            }
            case DirectiveKind::ElsIf:
                if (frames.empty() || frames.back().sawElse)
                    throwError("`elsif without matching `ifdef");
                frames.back().branches.push_back({directive, {}});
                break;
            case DirectiveKind::Else:
                if (frames.empty() || frames.back().sawElse)
                    throwError("`else without matching `ifdef");
                frames.back().sawElse = true;
                frames.back().branches.push_back({directive, {}});
                break;
            case DirectiveKind::EndIf: {
                if (frames.empty())
                    throwError("`endif without matching `ifdef");

                auto frame = std::move(frames.back());
                frames.pop_back();
                appendText(renderFrame(std::move(frame), directive, sourceText, macroValues));
                break;
            }
        }

        cursor = directive.end;
    }

    if (!frames.empty())
        throwError("unterminated conditional directive");

    appendText(sourceText.substr(cursor));

    return *this;
}
