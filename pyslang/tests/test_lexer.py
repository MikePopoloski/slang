import pytest

import pyslang


@pytest.fixture
def defaultLexer():
    sm = pyslang.SourceManager()
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
    return pyslang.Lexer(buf, pyslang.BumpAllocator(), pyslang.Diagnostics(), sm)


def test_lexer_lex(defaultLexer):
    tokens = []
    while (token := defaultLexer.lex()).kind != pyslang.TokenKind.EndOfFile:
        tokens.append(token)
    token_kinds = [t.kind for t in tokens]
    assert token_kinds == [
        pyslang.TokenKind.ModuleKeyword,
        pyslang.TokenKind.Identifier,
        pyslang.TokenKind.Semicolon,
        pyslang.TokenKind.Directive,
        pyslang.TokenKind.Identifier,
        pyslang.TokenKind.SystemIdentifier,
        pyslang.TokenKind.OpenParenthesis,
        pyslang.TokenKind.StringLiteral,
        pyslang.TokenKind.CloseParenthesis,
        pyslang.TokenKind.Semicolon,
        pyslang.TokenKind.Directive,
        pyslang.TokenKind.EndModuleKeyword,
    ]


def test_lexer_isNextTokenOnSameLine(defaultLexer):
    defaultLexer.lex()
    assert defaultLexer.isNextTokenOnSameLine()  # Identifier on same line as module
    defaultLexer.lex()
    defaultLexer.lex()
    assert not defaultLexer.isNextTokenOnSameLine()  # semicolon at end of line
