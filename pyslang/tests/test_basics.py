from pyslang import *


def test_numerics():
    assert SVInt(-3) == -3
    assert 99887766554433221100 == SVInt(99887766554433221100)
    assert clog2(99887766554433221100) == 67
    assert int(logic_t(0) | logic_t(1)) == 1
    assert int(SVInt("32'd1234")) == 1234

    cv = ConstantValue(3.14159)
    assert cv.value == 3.14159
    assert cv.isTrue()
    assert cv.convertToInt().value == 3

    r = ConstantRange(7, 1)
    assert str(r.reverse()) == "[1:7]"


def test_bag():
    lo = LexerOptions()
    po = ParserOptions()
    po.maxRecursionDepth = 4
    b = Bag([lo, po])
    assert b.parserOptions.maxRecursionDepth == 4
    assert b.compilationOptions is None


testFile = """
module m(input i, output o);
    assign o = (~i + 32'd1234);
endmodule
"""


def test_version():
    assert VersionInfo.getMajor() == 2


def test_sourcemanager():
    sm = SourceManager()
    buf = sm.assignText("coolfile.sv", testFile)

    filename = sm.getFileName(SourceLocation(buf.id, 0))
    assert filename == "coolfile.sv"


def test_syntax():
    tree = SyntaxTree.fromText(testFile)
    assert len(tree.diagnostics) == 0

    m = tree.root
    assert m.kind == SyntaxKind.ModuleDeclaration
    assert m.header.name.value == "m"

    a = m.members[0]
    assert a.kind == SyntaxKind.ContinuousAssign
    assert a.assignments[0].kind == SyntaxKind.AssignmentExpression

    zeroConst = a.assignments[0].right.expression.right
    assert zeroConst.kind == SyntaxKind.IntegerVectorExpression
    assert zeroConst.value.value == 1234


def test_compilation():
    tree = SyntaxTree.fromText(testFile)
    comp = Compilation()
    comp.addSyntaxTree(tree)

    diags = comp.getAllDiagnostics()
    assert len(diags) == 1
    assert diags[0].code == Diags.WidthTruncate

    report = DiagnosticEngine.reportAll(comp.sourceManager, diags)
    assert (
        ("\n" + report)
        == """
source:3:14: warning: implicit conversion truncates from 32 to 1 bits [-Wwidth-trunc]
    assign o = (~i + 32'd1234);
             ^  ~~~~~~~~~~~~~
"""
    )


def test_scriptsession():
    session = ScriptSession()
    session.eval('integer arr[string] = \'{"Hello":4, "World":8, default:-1};')
    session.eval(
        """
function int func(int i, integer arr[string]);
    case (i) inside
        [5'd1:5'd2]: return 1;
        arr: return 2;
    endcase
    return 3;
endfunction
"""
    )

    assert session.eval("func(4, arr)").value == 2
    assert len(session.getDiagnostics()) == 0
