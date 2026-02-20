# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pytest
from pyslang.parsing import Lexer, TokenKind

from pyslang import BumpAllocator, Diagnostics, SourceManager


@pytest.fixture
def defaultLexer():
    sm = SourceManager()
    buf = sm.assignText(
        "myfile.sv",
        """\
        module m;
            `ifdef MYDEFINE
            $display("in define");
            `endif
        endmodule
        """,
    )
    return Lexer(buf, BumpAllocator(), Diagnostics(), sm)


def test_lexer_lex(defaultLexer):
    tokens = []
    while (token := defaultLexer.lex()).kind != TokenKind.EndOfFile:
        tokens.append(token)
    token_kinds = [t.kind for t in tokens]
    assert token_kinds == [
        TokenKind.ModuleKeyword,
        TokenKind.Identifier,
        TokenKind.Semicolon,
        TokenKind.Directive,
        TokenKind.Identifier,
        TokenKind.SystemIdentifier,
        TokenKind.OpenParenthesis,
        TokenKind.StringLiteral,
        TokenKind.CloseParenthesis,
        TokenKind.Semicolon,
        TokenKind.Directive,
        TokenKind.EndModuleKeyword,
    ]


def test_lexer_isNextTokenOnSameLine(defaultLexer):
    defaultLexer.lex()
    assert defaultLexer.isNextTokenOnSameLine()  # Identifier on same line as module
    defaultLexer.lex()
    defaultLexer.lex()
    assert not defaultLexer.isNextTokenOnSameLine()  # semicolon at end of line
