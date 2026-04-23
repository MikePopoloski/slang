# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang.ast import (
    Compilation,
    GenerateBlockArraySymbol,
    GenerateBlockSymbol,
    GenerateBranchKind,
    SymbolKind,
)
from pyslang.syntax import SyntaxKind, SyntaxTree


def _compile(code):
    tree, comp = SyntaxTree.fromText(code), Compilation()
    comp.addSyntaxTree(tree)
    # Force elaboration diagnostics so all provenance is populated.
    comp.getAllDiagnostics()
    return comp


def test_if_generate_provenance():
    comp = _compile("""
module Top #(parameter int MODE = 1)();
    if (MODE == 1) begin : if_true
        int a;
    end
    else begin : if_false
        int b;
    end
endmodule
""")

    root = comp.getRoot()
    if_true = root.lookupName("Top.if_true")
    if_false = root.lookupName("Top.if_false")

    assert isinstance(if_true, GenerateBlockSymbol)
    assert isinstance(if_false, GenerateBlockSymbol)

    assert if_true.branchKind == GenerateBranchKind.IfTrue
    assert if_false.branchKind == GenerateBranchKind.IfFalse
    assert not if_true.isUninstantiated
    assert if_false.isUninstantiated

    assert if_true.conditionExpression is not None
    # Both arms share the same bound condition object.
    assert if_true.conditionExpression is if_false.conditionExpression
    assert len(if_true.caseItemExpressions) == 0

    assert if_true.generateConstructSyntax is not None
    assert if_true.generateConstructSyntax.kind == SyntaxKind.IfGenerate
    assert if_true.generateConstructSyntax is if_false.generateConstructSyntax


def test_directly_nested_if_generate_preserves_structure():
    # Inner if is unbracketed; LRM flattens it into the outer scope.
    comp = _compile("""
module Top #(parameter int A = 1, parameter int B = 1)();
    if (A == 1)
        if (B == 1) begin : t
            int x;
        end
        else begin : f
            int y;
        end
endmodule
""")

    root = comp.getRoot()
    t = root.lookupName("Top.t")
    f = root.lookupName("Top.f")

    assert t.generateConstructSyntax is not None
    assert t.generateConstructSyntax.kind == SyntaxKind.IfGenerate
    assert t.generateConstructSyntax is f.generateConstructSyntax

    # Outer construct reachable via syntax-parent walk.
    outer = t.generateConstructSyntax.parent
    assert outer is not None
    assert outer.kind == SyntaxKind.IfGenerate
    assert outer is not t.generateConstructSyntax


def test_case_generate_provenance():
    comp = _compile("""
module Top #(parameter int MODE = 1)();
    case (MODE)
        1, 2: begin : case_item_lo
            int c;
        end
        default: begin : case_default
            int d;
        end
    endcase
endmodule
""")

    root = comp.getRoot()
    case_item = root.lookupName("Top.case_item_lo")
    case_default = root.lookupName("Top.case_default")

    assert case_item.branchKind == GenerateBranchKind.CaseItem
    assert case_default.branchKind == GenerateBranchKind.CaseDefault
    assert case_item.conditionExpression is not None
    assert case_item.conditionExpression is case_default.conditionExpression
    assert len(case_item.caseItemExpressions) == 2
    assert len(case_default.caseItemExpressions) == 0


def test_loop_generate_provenance():
    comp = _compile("""
module Top;
    genvar g;
    for (g = 0; g < 3; g = g + 1) begin : arr
        int e;
    end
endmodule
""")

    arr = comp.getRoot().lookupName("Top.arr")
    assert isinstance(arr, GenerateBlockArraySymbol)
    assert arr.initialExpression is not None
    assert arr.stopExpression is not None
    assert arr.iterExpression is not None
    assert arr.genvar is not None
    assert arr.genvar.kind == SymbolKind.Genvar
    assert arr.genvar.name == "g"

    assert len(arr.entries) == 3
    for entry in arr.entries:
        assert entry.branchKind == GenerateBranchKind.LoopIteration


def test_loop_generate_inline_genvar():
    comp = _compile("""
module Top;
    for (genvar i = 0; i < 2; i = i + 1) begin : arr
        int x;
    end
endmodule
""")

    arr = comp.getRoot().lookupName("Top.arr")
    assert arr.genvar is not None
    assert arr.genvar.kind == SymbolKind.Genvar
    assert arr.genvar.name == "i"
    assert len(arr.entries) == 2
