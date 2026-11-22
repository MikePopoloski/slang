# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pathlib import Path

import pytest
from pyslang.analysis import AnalysisManager
from pyslang.ast import (
    ASTContext,
    ChargeStrength,
    Compilation,
    Delay3Control,
    DelayControl,
    DriveStrength,
    EvalContext,
    Lookup,
    LookupLocation,
    Scope,
    ScriptSession,
    SymbolKind,
)
from pyslang.parsing import LexerOptions, ParserOptions
from pyslang.syntax import SyntaxKind, SyntaxTree

from pyslang import (
    Bag,
    ConstantRange,
    ConstantValue,
    DiagnosticEngine,
    Diags,
    SourceLocation,
    SourceManager,
    SVInt,
    TimeScaleMagnitude,
    TimeScaleValue,
    TimeUnit,
    clog2,
    logic_t,
)

testFile = """
module m(input i, output o);
    assign #2 o = (~i + 32'd1234);
endmodule
"""


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


def test_source_manager():
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
    assert len(diags) == 2
    assert diags[0].code == Diags.WidthTruncate
    assert diags[1].code == Diags.ArithOpMismatch

    report = DiagnosticEngine.reportAll(comp.sourceManager, diags)
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


def test_simulation_time_unit():
    # With nothing specified the simulation time unit is the default precision.
    assert Compilation().simulationTimeUnit == TimeScaleValue.fromString("1ns")

    tree = SyntaxTree.fromText(
        """
timeunit 100ps / 10fs;
module a; timeunit 1ms / 1us; endmodule
`timescale 1ns / 1ps
module b; endmodule
"""
    )
    comp = Compilation()
    comp.addSyntaxTree(tree)

    # The smallest precision anywhere in the design.
    unit = comp.simulationTimeUnit
    assert unit == TimeScaleValue(TimeUnit.Femtoseconds, TimeScaleMagnitude.Ten)
    assert str(unit) == "10fs"


def test_resolved_dpi_exports():
    tree = SyntaxTree.fromText("""
module m;
    function void f1; endfunction
    function void f2; endfunction
    export "DPI-C" function f1;
    export "DPI-C" my_f2 = function f2;
endmodule
""")
    comp = Compilation()
    comp.addSyntaxTree(tree)
    assert len(comp.getAllDiagnostics()) == 0

    exports = comp.getDPIExports()
    assert len(exports) == 2
    assert exports[0].subroutine.name == "f1"
    assert exports[0].cIdentifier == "f1"
    assert exports[0].syntax is not None
    assert exports[0].syntax.kind == SyntaxKind.DPIExport
    assert exports[1].subroutine.name == "f2"
    assert exports[1].cIdentifier == "my_f2"
    assert exports[1].syntax is not None
    assert exports[1].syntax.kind == SyntaxKind.DPIExport


def test_include_metadata():
    tree = SyntaxTree.fromText(
        f"""
    `include "{Path(__file__).parent}/some_file.svh"
    """
    )
    includes = tree.getIncludeDirectives()
    assert len(includes) == 1
    assert includes[0].path.endswith("some_file.svh")


def test_script_session():
    session = ScriptSession()
    session.eval("""integer arr[string] = '{"Hello":4, "World":8, default:-1};""")
    session.eval("""
function int func(int i, integer arr[string]);
    case (i) inside
        [32'sd1:32'sd2]: return 1;
        arr: return 2;
    endcase
    return 3;
endfunction
""")

    assert session.eval("func(4, arr)").value == 2

    # Missing 'default' in case statement. Check that the diagnostic is reported.
    assert len(session.getDiagnostics()) == 1
    assert session.getDiagnostics()[0].code == Diags.CaseDefault


def test_symbol_inspection():
    comp = Compilation()
    comp.addSyntaxTree(SyntaxTree.fromText(testFile))

    m = comp.getRoot().lookupName("m")
    a = m.body[4]
    assert a.kind == SymbolKind.ContinuousAssign
    assert a.delay.expr.value == 2

    t = a.assignment.right.operand.right.type
    assert t.isPackedArray
    assert t.bitWidth == 32
    assert str(t) == "logic[31:0]"


def test_scope_symbol_conversion():
    """Symbols that are scopes can be passed where a Scope is expected (#1988)."""
    comp = Compilation()
    comp.addSyntaxTree(SyntaxTree.fromText(testFile))

    body = comp.getRoot().topInstances[0].body
    port = body.find("i")
    assert port.parentScope is not None

    # Explicit conversion yields the same scope that members report as their parent.
    scope = Scope(body)
    assert isinstance(scope, Scope)
    assert scope == port.parentScope
    assert hash(scope) == hash(port.parentScope)
    assert scope.find("i") == port

    # Implicit conversion for both reference and pointer parameters.
    assert port.parentScope == body
    assert ASTContext(body, LookupLocation.max).scope == scope
    assert LookupLocation(body, 0).scope == scope
    assert Lookup.isVisibleFrom(port, body)
    assert AnalysisManager().getAnalyzedScope(body) is None

    # Symbols that aren't scopes are still rejected.
    with pytest.raises(TypeError):
        Scope(port)
    with pytest.raises(TypeError):
        ASTContext(port, LookupLocation.max)


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

    tree = SyntaxTree.fromText(input_str)
    output_str = str(tree.root)

    assert input_str.rstrip() == output_str.rstrip()


def test_declaring_package_and_eval_context():
    tree = SyntaxTree.fromText("""
package p;
    function automatic int sum(int n);
        int s = 0;
        for (int i = 0; i < n; i++) s += i;
        return s;
    endfunction
endpackage

module m;
    localparam int P = p::sum(100);
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    assert not compilation.getAllDiagnostics()

    pkg = compilation.getPackage("p")
    sub = pkg.find("sum")
    assert sub.declaringPackage.name == "p"
    assert pkg.declaringPackage.name == "p"
    m = compilation.getRoot().lookupName("m")
    assert m.declaringPackage is None
    assert m.body.find("P").value == 4950

    ec = EvalContext(m.body)
    assert ec.steps == 0
    assert ec.callDepth == 0
    assert ec.diagCount == 0
    assert ec.tryAddSteps(5)
    assert ec.steps == 5
    assert not ec.tryAddSteps(compilation.options.maxConstexprSteps)
    assert ec.steps == 5

    ec.preventMemoization()
    assert ec.takeMemoizationPrevented()
    assert not ec.takeMemoizationPrevented()


def test_drive_and_charge_strengths():
    tree = SyntaxTree.fromText("""
module m(input logic a, b, output logic y, z);
    and (strong1, strong0) g1 (y, a, b);
    and #(1:2:3) g2 (z, a, b);
    wire (weak0, pull1) #2 w = a;
    trireg (large) t;
    assign (supply0, highz1) y = a;
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    assert not compilation.getAllDiagnostics()

    body = compilation.getRoot().lookupName("m").body
    assert body.find("g1").driveStrength == (DriveStrength.Strong, DriveStrength.Strong)
    assert body.find("g2").driveStrength == (None, None)
    assert isinstance(body.find("g2").delay, Delay3Control)

    w = body.find("w")
    assert w.driveStrength == (DriveStrength.Weak, DriveStrength.Pull)
    assert isinstance(w.delay, DelayControl)
    assert w.chargeStrength is None
    assert body.find("t").chargeStrength == ChargeStrength.Large

    assign = next(s for s in body if s.kind == SymbolKind.ContinuousAssign)
    assert assign.driveStrength == (DriveStrength.Supply, DriveStrength.HighZ)
