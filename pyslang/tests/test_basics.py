# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pathlib import Path

import pyslang


def test_numerics():
    assert pyslang.SVInt(-3) == -3
    assert 99887766554433221100 == pyslang.SVInt(99887766554433221100)
    assert pyslang.clog2(99887766554433221100) == 67
    assert int(pyslang.logic_t(0) | pyslang.logic_t(1)) == 1
    assert int(pyslang.SVInt("32'd1234")) == 1234

    cv = pyslang.ConstantValue(3.14159)
    assert cv.value == 3.14159
    assert cv.isTrue()
    assert cv.convertToInt().value == 3

    r = pyslang.ConstantRange(7, 1)
    assert str(r.reverse()) == "[1:7]"


def test_bag():
    lo = pyslang.LexerOptions()
    po = pyslang.ParserOptions()
    po.maxRecursionDepth = 4
    b = pyslang.Bag([lo, po])
    assert b.parserOptions.maxRecursionDepth == 4
    assert b.compilationOptions is None


testFile = """
module m(input i, output o);
    assign #2 o = (~i + 32'd1234);
endmodule
"""


def test_source_manager():
    sm = pyslang.SourceManager()
    buf = sm.assignText("coolfile.sv", testFile)

    filename = sm.getFileName(pyslang.SourceLocation(buf.id, 0))
    assert filename == "coolfile.sv"


def test_syntax():
    tree = pyslang.SyntaxTree.fromText(testFile)
    assert len(tree.diagnostics) == 0

    m = tree.root
    assert m.kind == pyslang.SyntaxKind.ModuleDeclaration
    assert m.header.name.value == "m"

    a = m.members[0]
    assert a.kind == pyslang.SyntaxKind.ContinuousAssign
    assert a.assignments[0].kind == pyslang.SyntaxKind.AssignmentExpression

    zeroConst = a.assignments[0].right.expression.right
    assert zeroConst.kind == pyslang.SyntaxKind.IntegerVectorExpression
    assert zeroConst.value.value == 1234


def test_compilation():
    tree = pyslang.SyntaxTree.fromText(testFile)
    comp = pyslang.Compilation()
    comp.addSyntaxTree(tree)

    diags = comp.getAllDiagnostics()
    assert len(diags) == 2
    assert diags[0].code == pyslang.Diags.WidthTruncate
    assert diags[1].code == pyslang.Diags.ArithOpMismatch

    report = pyslang.DiagnosticEngine.reportAll(comp.sourceManager, diags)
    assert (
        ("\n" + report)
        == """
source:3:20: warning: implicit conversion truncates from 32 to 1 bits [-Wwidth-trunc]
    assign #2 o = (~i + 32'd1234);
                ~  ^~~~~~~~~~~~~
source:3:23: warning: arithmetic between operands of different types ('logic' and 'bit[31:0]') [-Warith-op-mismatch]
    assign #2 o = (~i + 32'd1234);
                   ~~ ^ ~~~~~~~~
"""
    )


def test_include_metadata():
    tree = pyslang.SyntaxTree.fromText(
        """
    `include "{}/some_file.svh"
    """.format(
            Path(__file__).parent
        )
    )
    includes = tree.getIncludeDirectives()
    assert len(includes) == 1
    assert includes[0].path.endswith("some_file.svh")


def test_script_session():
    session = pyslang.ScriptSession()
    session.eval("""integer arr[string] = '{"Hello":4, "World":8, default:-1};""")
    session.eval(
        """
function int func(int i, integer arr[string]);
    case (i) inside
        [32'sd1:32'sd2]: return 1;
        arr: return 2;
    endcase
    return 3;
endfunction
"""
    )

    assert session.eval("func(4, arr)").value == 2

    # Missing 'default' in case statement. Check that the diagnostic is reported.
    assert len(session.getDiagnostics()) == 1
    assert session.getDiagnostics()[0].code == pyslang.Diags.CaseDefault


def test_symbol_inspection():
    comp = pyslang.Compilation()
    comp.addSyntaxTree(pyslang.SyntaxTree.fromText(testFile))

    m = comp.getRoot().lookupName("m")
    a = m.body[4]
    assert a.kind == pyslang.SymbolKind.ContinuousAssign
    assert a.delay.expr.value == 2

    t = a.assignment.right.operand.right.type
    assert t.isPackedArray
    assert t.bitWidth == 32
    assert str(t) == "logic[31:0]"


def test_string_to_ast_to_string_loop() -> None:
    """Test that converting a string to a SyntaxTree and back gives the original string."""
    input_str = """
        module and_gate (
            input wire x,
            input wire y,
            output wire z
        );
            assign z = x & y;
        endmodule
    """

    ast = pyslang.SyntaxTree.fromText(input_str)
    output_str = str(ast.root)

    assert input_str.rstrip() == output_str.rstrip()
