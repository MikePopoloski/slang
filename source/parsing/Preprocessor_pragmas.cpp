//------------------------------------------------------------------------------
// Preprocessor_pragmas.cpp
// Pragma-related preprocessor support
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace slang {

std::pair<PragmaExpressionSyntax*, bool> Preprocessor::parsePragmaExpression() {
    Token token = peek();
    if (token.kind == TokenKind::Identifier || LexerFacts::isKeyword(token.kind)) {
        auto name = consume();
        if (peek().kind == TokenKind::Equals) {
            auto equals = consume();
            auto [expr, succeeded] = parsePragmaValue();
            auto result = alloc.emplace<NameValuePragmaExpressionSyntax>(name, equals, *expr);
            return { result, succeeded };
        }

        return { alloc.emplace<SimplePragmaExpressionSyntax>(name), true };
    }

    return parsePragmaValue();
}

std::pair<PragmaExpressionSyntax*, bool> Preprocessor::parsePragmaValue() {
    if (auto pair = checkNextPragmaToken(); !pair.second)
        return pair;

    Token token = peek();
    if (token.kind == TokenKind::IntegerBase || token.kind == TokenKind::IntegerLiteral) {
        PragmaExpressionSyntax* expr;
        auto result = numberParser.parseInteger(*this);
        if (result.isSimple) {
            expr = alloc.emplace<SimplePragmaExpressionSyntax>(result.value);
        }
        else {
            expr =
                alloc.emplace<NumberPragmaExpressionSyntax>(result.size, result.base, result.value);
        }

        return { expr, true };
    }

    if (token.kind == TokenKind::RealLiteral) {
        auto result = numberParser.parseReal(*this);
        return { alloc.emplace<SimplePragmaExpressionSyntax>(result), true };
    }

    if (token.kind == TokenKind::Identifier || token.kind == TokenKind::StringLiteral ||
        LexerFacts::isKeyword(token.kind)) {
        return { alloc.emplace<SimplePragmaExpressionSyntax>(consume()), true };
    }

    if (token.kind != TokenKind::OpenParenthesis) {
        addDiag(diag::ExpectedPragmaExpression, token.location());

        auto expected = Token::createMissing(alloc, TokenKind::Identifier, token.location());
        return { alloc.emplace<SimplePragmaExpressionSyntax>(expected), false };
    }

    SmallVectorSized<TokenOrSyntax, 4> values;
    Token openParen = consume();
    bool wantComma = false;
    bool ok = false;

    // This keeps track of the last real token we've consumed before
    // breaking from the loop; if there's an error it's possible we've
    // gone on and parsed more directives into the resulting token,
    // so this is necessary to correctly place the diagnostic.
    Token lastToken = openParen;

    token = peek();
    while (token.kind != TokenKind::EndOfFile && token.isOnSameLine()) {
        if (wantComma) {
            if (token.kind == TokenKind::CloseParenthesis) {
                ok = true;
                break;
            }

            Token comma = expect(TokenKind::Comma);
            values.append(comma);
            wantComma = false;
            lastToken = comma;
        }
        else {
            auto [expr, succeeded] = parsePragmaExpression();
            values.append(expr);
            wantComma = true;

            if (!succeeded)
                break;

            lastToken = expr->getLastToken();
        }
        token = peek();
    }

    token = peek();
    Token closeParen;
    if (token.kind == TokenKind::CloseParenthesis && token.isOnSameLine()) {
        closeParen = consume();
    }
    else {
        closeParen = Token::createExpected(alloc, diagnostics, token, TokenKind::CloseParenthesis,
                                           lastToken, Token());
    }

    return { alloc.emplace<ParenPragmaExpressionSyntax>(openParen, values.copy(alloc), closeParen),
             ok };
}

std::pair<PragmaExpressionSyntax*, bool> Preprocessor::checkNextPragmaToken() {
    if (!peek().isOnSameLine()) {
        auto loc = lastConsumed.location() + lastConsumed.rawText().length();
        addDiag(diag::ExpectedPragmaExpression, loc);

        auto expected = Token::createMissing(alloc, TokenKind::Identifier, loc);
        return { alloc.emplace<SimplePragmaExpressionSyntax>(expected), false };
    }
    return { nullptr, true };
}

void Preprocessor::handleExponentSplit(Token token, size_t offset) {
    // This is called by NumberParser to handle an error case, for example
    // in the snippet 'h 3e+2 the +2 is not part of the number. We should
    // just report an error and move on.
    addDiag(diag::ExpectedPragmaExpression, token.location() + offset);
}

void Preprocessor::applyPragma(const PragmaDirectiveSyntax& pragma) {
    string_view name = pragma.name.valueText();
    if (name == "protect") {
        applyProtectPragma(pragma);
        return;
    }

    if (name == "reset") {
        applyResetPragma(pragma);
        return;
    }

    if (name == "resetall") {
        applyResetAllPragma(pragma);
        return;
    }

    if (name == "once") {
        applyOncePragma(pragma);
        return;
    }

    if (name == "diagnostic") {
        applyDiagnosticPragma(pragma);
        return;
    }

    // Otherwise, if the pragma is unknown warn and ignore.
    addDiag(diag::UnknownPragma, pragma.name.range()) << name;
}

void Preprocessor::applyProtectPragma(const PragmaDirectiveSyntax& pragma) {
    if (pragma.args.empty()) {
        Token last = pragma.getLastToken();
        addDiag(diag::ExpectedProtectKeyword, last.location() + last.rawText().length());
        return;
    }

    auto handle = [&](Token keyword, const PragmaExpressionSyntax* args) {
        auto text = keyword.valueText();
        if (auto it = pragmaProtectHandlers.find(text); it != pragmaProtectHandlers.end())
            (this->*(it->second))(keyword, args);
        else if (!text.empty())
            addDiag(diag::UnknownProtectKeyword, keyword.range()) << text;
    };

    for (auto arg : pragma.args) {
        if (arg->kind == SyntaxKind::SimplePragmaExpression) {
            auto& simple = arg->as<SimplePragmaExpressionSyntax>();
            handle(simple.value, nullptr);
        }
        else if (arg->kind == SyntaxKind::NameValuePragmaExpression) {
            auto& nvp = arg->as<NameValuePragmaExpressionSyntax>();
            handle(nvp.name, nvp.value);
        }
        else {
            addDiag(diag::ExpectedProtectKeyword, arg->sourceRange());
        }
    }
}

void Preprocessor::applyResetPragma(const PragmaDirectiveSyntax& pragma) {
    // Just check that we know about the names being reset, and warn if we don't.
    for (auto arg : pragma.args) {
        if (arg->kind == SyntaxKind::SimplePragmaExpression) {
            auto& simple = arg->as<SimplePragmaExpressionSyntax>();
            if (simple.value.kind == TokenKind::Identifier) {
                string_view name = simple.value.rawText();
                if (!name.empty() && name != "protect" && name != "once" && name != "diagnostic")
                    addDiag(diag::UnknownPragma, simple.value.range()) << name;

                // Nothing to do here, we don't support any pragmas that can be reset.
                continue;
            }
        }

        // Otherwise this isn't even a pragma name, so it's ill-formed.
        addDiag(diag::ExpectedPragmaName, arg->sourceRange());
    }
}

void Preprocessor::applyResetAllPragma(const PragmaDirectiveSyntax& pragma) {
    // Nothing to do here, we don't support any pragmas that can be reset.
    // Just check that there aren't any extraneous arguments.
    ensurePragmaArgs(pragma, 0);
}

void Preprocessor::applyOncePragma(const PragmaDirectiveSyntax& pragma) {
    ensurePragmaArgs(pragma, 0);

    auto text = sourceManager.getSourceText(pragma.directive.location().buffer());
    if (!text.empty())
        includeOnceHeaders.emplace(text.data());
}

void Preprocessor::applyDiagnosticPragma(const PragmaDirectiveSyntax& pragma) {
    if (pragma.args.empty()) {
        Token last = pragma.getLastToken();
        addDiag(diag::ExpectedDiagPragmaArg, last.location() + last.rawText().length());
        return;
    }

    for (auto arg : pragma.args) {
        if (arg->kind == SyntaxKind::SimplePragmaExpression) {
            auto& simple = arg->as<SimplePragmaExpressionSyntax>();
            string_view action = simple.value.rawText();
            if (simple.value.kind == TokenKind::Identifier && action == "push") {
                sourceManager.addDiagnosticDirective(simple.value.location(), "__push__",
                                                     DiagnosticSeverity::Ignored);
            }
            else if (simple.value.kind == TokenKind::Identifier && action == "pop") {
                sourceManager.addDiagnosticDirective(simple.value.location(), "__pop__",
                                                     DiagnosticSeverity::Ignored);
            }
            else {
                addDiag(diag::UnknownDiagPragmaArg, simple.value.range()) << action;
            }
        }
        else if (arg->kind == SyntaxKind::NameValuePragmaExpression) {
            auto& nvp = arg->as<NameValuePragmaExpressionSyntax>();

            DiagnosticSeverity severity;
            string_view text = nvp.name.valueText();
            if (text == "ignore")
                severity = DiagnosticSeverity::Ignored;
            else if (text == "warn")
                severity = DiagnosticSeverity::Warning;
            else if (text == "error")
                severity = DiagnosticSeverity::Error;
            else if (text == "fatal")
                severity = DiagnosticSeverity::Fatal;
            else {
                addDiag(diag::ExpectedDiagPragmaLevel, nvp.name.range());
                continue;
            }

            auto setDirective = [&](const PragmaExpressionSyntax& expr) {
                if (expr.kind == SyntaxKind::SimplePragmaExpression) {
                    auto& simple = expr.as<SimplePragmaExpressionSyntax>();
                    if (simple.value.kind == TokenKind::StringLiteral) {
                        sourceManager.addDiagnosticDirective(simple.value.location(),
                                                             simple.value.valueText(), severity);
                    }
                    else {
                        addDiag(diag::ExpectedDiagPragmaArg, simple.value.range());
                    }
                }
                else {
                    addDiag(diag::ExpectedDiagPragmaArg, expr.sourceRange());
                }
            };

            if (nvp.value->kind == SyntaxKind::ParenPragmaExpression) {
                auto& paren = nvp.value->as<ParenPragmaExpressionSyntax>();
                for (auto value : paren.values)
                    setDirective(*value);
            }
            else {
                setDirective(*nvp.value);
            }
        }
        else {
            addDiag(diag::ExpectedDiagPragmaArg, arg->sourceRange());
        }
    }
}

void Preprocessor::ensurePragmaArgs(const PragmaDirectiveSyntax& pragma, size_t count) {
    if (pragma.args.size() > count) {
        auto& diag = addDiag(diag::ExtraPragmaArgs, pragma.args[count]->getFirstToken().location());
        diag << pragma.name.valueText();
    }
}

void Preprocessor::ensureNoPragmaArgs(Token keyword, const PragmaExpressionSyntax* args) {
    if (args) {
        auto& diag = addDiag(diag::ExtraPragmaArgs, args->sourceRange());
        diag << keyword.valueText();
    }
}

optional<uint32_t> Preprocessor::requireUInt32(const PragmaExpressionSyntax& expr) {
    auto checkResult = [&](const SVInt& svi) -> optional<uint32_t> {
        auto value = svi.as<int32_t>();
        if (!value || *value < 0) {
            addDiag(diag::InvalidPragmaNumber, expr.sourceRange());
            return {};
        }

        return uint32_t(*value);
    };

    if (expr.kind == SyntaxKind::SimplePragmaExpression) {
        auto token = expr.as<SimplePragmaExpressionSyntax>().value;
        if (token.kind == TokenKind::IntegerLiteral)
            return checkResult(token.intValue());
        else if (token.kind == TokenKind::RealLiteral)
            return checkResult(SVInt::fromDouble(32, token.realValue(), true));
    }
    else if (expr.kind == SyntaxKind::NumberPragmaExpression) {
        return checkResult(expr.as<NumberPragmaExpressionSyntax>().value.intValue());
    }

    addDiag(diag::InvalidPragmaNumber, expr.sourceRange());
    return {};
}

void Preprocessor::handleProtectBegin(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    if (protectEncryptDepth)
        addDiag(diag::NestedProtectBegin, keyword.range());
    protectEncryptDepth++;
}

void Preprocessor::handleProtectEnd(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    if (protectEncryptDepth)
        protectEncryptDepth--;
    else
        addDiag(diag::ExtraProtectEnd, keyword.range()) << keyword.valueText();
}

void Preprocessor::handleProtectBeginProtected(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);
    protectDecryptDepth++;
}

void Preprocessor::handleProtectEndProtected(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    if (protectDecryptDepth)
        protectDecryptDepth--;
    else
        addDiag(diag::ExtraProtectEnd, keyword.range()) << keyword.valueText();
}

void Preprocessor::handleProtectSingleArgIgnore(Token keyword, const PragmaExpressionSyntax* args) {
    if (!args || args->kind != SyntaxKind::SimplePragmaExpression ||
        args->as<SimplePragmaExpressionSyntax>().value.kind != TokenKind::StringLiteral) {

        SourceRange range = args ? args->sourceRange() : keyword.range();
        addDiag(diag::ExpectedProtectArg, range) << keyword.valueText();
    }
}

void Preprocessor::handleProtectEncoding(Token keyword, const PragmaExpressionSyntax* args) {
    if (!args || args->kind != SyntaxKind::ParenPragmaExpression ||
        args->as<ParenPragmaExpressionSyntax>().values.empty()) {
        addDiag(diag::ProtectArgList, args ? args->sourceRange() : keyword.range())
            << keyword.valueText();
        return;
    }

    for (auto arg : args->as<ParenPragmaExpressionSyntax>().values) {
        if (arg->kind != SyntaxKind::NameValuePragmaExpression) {
            addDiag(diag::ProtectArgList, arg->sourceRange()) << keyword.valueText();
            continue;
        }

        auto& nvp = arg->as<NameValuePragmaExpressionSyntax>();
        auto name = nvp.name.valueText();
        if (name == "enctype"sv) {
            auto value = nvp.value->getFirstToken();

            std::string valueText(value.valueText());
            strToLower(valueText);

            if (valueText == "uuencode"sv) {
                protectEncoding = ProtectEncoding::UUEncode;
            }
            else if (valueText == "base64"sv) {
                protectEncoding = ProtectEncoding::Base64;
            }
            else if (valueText == "quoted-printable"sv) {
                protectEncoding = ProtectEncoding::QuotedPrintable;
            }
            else if (valueText == "raw"sv) {
                protectEncoding = ProtectEncoding::Raw;
            }
            else {
                protectEncoding = ProtectEncoding::Raw;
                addDiag(diag::UnknownProtectEncoding, value.range()) << value.valueText();
            }
        }
        else if (name == "line_length"sv) {
            if (auto num = requireUInt32(*nvp.value))
                protectLineLength = *num;
        }
        else if (name == "bytes"sv) {
            if (auto num = requireUInt32(*nvp.value))
                protectBytes = *num;
        }
        else if (!name.empty()) {
            addDiag(diag::UnknownProtectOption, nvp.name.range()) << keyword.valueText() << name;
        }
    }
}

void Preprocessor::handleProtectKey(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    // TODO: skip the key
}

void Preprocessor::handleProtectBlock(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    // TODO: skip the block
}

void Preprocessor::handleProtectLicense(Token keyword, const PragmaExpressionSyntax* args) {
    if (!args || args->kind != SyntaxKind::ParenPragmaExpression ||
        args->as<ParenPragmaExpressionSyntax>().values.empty()) {
        addDiag(diag::ProtectArgList, args ? args->sourceRange() : keyword.range())
            << keyword.valueText();
        return;
    }

    for (auto arg : args->as<ParenPragmaExpressionSyntax>().values) {
        if (arg->kind != SyntaxKind::NameValuePragmaExpression) {
            addDiag(diag::ProtectArgList, arg->sourceRange()) << keyword.valueText();
            continue;
        }

        auto& nvp = arg->as<NameValuePragmaExpressionSyntax>();
        auto name = nvp.name.valueText();
        if (name == "library"sv || name == "entry"sv || name == "feature"sv || name == "exit"sv) {
            if (nvp.value->kind != SyntaxKind::SimplePragmaExpression ||
                nvp.value->as<SimplePragmaExpressionSyntax>().value.kind !=
                    TokenKind::StringLiteral) {
                addDiag(diag::ExpectedProtectArg, nvp.value->sourceRange()) << name;
            }
        }
        else if (name == "match"sv) {
            requireUInt32(*nvp.value);
        }
        else if (!name.empty()) {
            addDiag(diag::UnknownProtectOption, nvp.name.range()) << keyword.valueText() << name;
        }
    }
}

void Preprocessor::handleProtectReset(Token keyword, const PragmaExpressionSyntax* args) {
    ensureNoPragmaArgs(keyword, args);

    // TODO: handle the reset
}

void Preprocessor::handleProtectViewport(Token keyword, const PragmaExpressionSyntax* args) {
    if (!args || args->kind != SyntaxKind::ParenPragmaExpression ||
        args->as<ParenPragmaExpressionSyntax>().values.size() != 2) {
        addDiag(diag::InvalidPragmaViewport, args ? args->sourceRange() : keyword.range());
        return;
    }

    auto checkOption = [&](size_t index, string_view name) {
        auto syntax = args->as<ParenPragmaExpressionSyntax>().values[index];
        if (syntax->kind != SyntaxKind::NameValuePragmaExpression) {
            addDiag(diag::InvalidPragmaViewport, syntax->sourceRange());
            return false;
        }

        auto& nvp = syntax->as<NameValuePragmaExpressionSyntax>();
        if (nvp.name.valueText() != name) {
            addDiag(diag::InvalidPragmaViewport, nvp.name.range());
            return false;
        }

        if (nvp.value->kind != SyntaxKind::SimplePragmaExpression ||
            nvp.value->as<SimplePragmaExpressionSyntax>().value.kind != TokenKind::StringLiteral) {
            addDiag(diag::InvalidPragmaViewport, nvp.value->sourceRange());
            return false;
        }

        return true;
    };

    if (!checkOption(0, "object"sv))
        return;

    checkOption(1, "access"sv);
}

} // namespace slang
