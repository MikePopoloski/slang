# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pyslang

testfile = """
//! Module description
//! ***this is code*** sample
//! | Tables   |     Are      |  Cool |
//! |----------|:------------:|------:|
//! | col 1 is | left-aligned | $1600 |

module gray_counter (
    out    , // counter out
    clk    , //! clock
    clk1   , //! clock sample
    rst      //! **active high reset**
    );

    input clk, clk1, rst;
    output [7:0] out;
    wire [7:0] out;
    reg [7:0] count;

endmodule
"""


def test_extract_comments():
    tree = pyslang.SyntaxTree.fromText(testfile)
    assert tree.root.kind == pyslang.SyntaxKind.ModuleDeclaration

    moduleComments = []
    for t in tree.root.getFirstToken().trivia:
        if t.kind == pyslang.TriviaKind.LineComment:
            comment = t.getRawText()
            if comment.startswith("//!"):
                moduleComments.append(comment[3:].strip())

    portComments = {}
    portList = tree.root.header.ports
    lastPort = None

    def getLeadingComments(tok):
        if lastPort is not None:
            for t in tok.trivia:
                if t.kind == pyslang.TriviaKind.LineComment:
                    comment = t.getRawText()
                    if comment.startswith("//!"):
                        portComments[lastPort].append(comment[3:].strip())
                elif t.kind == pyslang.TriviaKind.EndOfLine:
                    break

    if portList is not None:
        for port in portList.ports:
            if isinstance(port, pyslang.ImplicitNonAnsiPortSyntax):
                tok = port.getFirstToken()
                getLeadingComments(tok)

                portName = tok.value
                portComments[portName] = []
                lastPort = portName

        getLeadingComments(portList.closeParen)

    assert len(moduleComments) == 5
    assert moduleComments[4] == "| col 1 is | left-aligned | $1600 |"

    for k, _ in portComments.copy().items():
        if len(portComments[k]) == 0:
            del portComments[k]

    assert len(portComments) == 3
    assert portComments["rst"][0] == "**active high reset**"
