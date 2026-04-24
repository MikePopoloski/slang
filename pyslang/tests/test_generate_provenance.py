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


_CONSTRUCT_KINDS = {SyntaxKind.IfGenerate, SyntaxKind.CaseGenerate, SyntaxKind.LoopGenerate}


def _construct_of(block):
    # Walks up through any ElseClause / StandardCaseItem / DefaultCaseItem
    # wrapper to the enclosing if/case/loop-generate node.
    syntax = block.syntax
    node = syntax.parent if syntax is not None else None
    while node is not None and node.kind not in _CONSTRUCT_KINDS:
        node = node.parent
    return node


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
    # Conditional branches never expose a loop index.
    assert if_true.arrayIndex is None
    assert if_false.arrayIndex is None

    true_construct = _construct_of(if_true)
    false_construct = _construct_of(if_false)
    assert true_construct is not None
    assert true_construct.kind == SyntaxKind.IfGenerate
    assert true_construct is false_construct


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

    inner_if = _construct_of(t)
    assert inner_if is not None
    assert inner_if.kind == SyntaxKind.IfGenerate
    assert inner_if is _construct_of(f)

    # The directly-nested outer construct is reachable by continuing the walk.
    outer = inner_if.parent
    while outer is not None and outer.kind != SyntaxKind.IfGenerate:
        outer = outer.parent
    assert outer is not None
    assert outer is not inner_if


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
    assert case_item.arrayIndex is None

    case_construct = _construct_of(case_item)
    assert case_construct is not None
    assert case_construct.kind == SyntaxKind.CaseGenerate
    assert case_construct is _construct_of(case_default)


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

    # The loop array's own syntax is the LoopGenerateSyntax directly.
    assert arr.syntax is not None
    assert arr.syntax.kind == SyntaxKind.LoopGenerate

    assert len(arr.entries) == 3
    for entry in arr.entries:
        assert entry.branchKind == GenerateBranchKind.LoopIteration
        assert entry.arrayIndex is not None
        assert entry.conditionExpression is None
        # Each entry's syntax parent walks back to the LoopGenerateSyntax.
        assert _construct_of(entry) is arr.syntax


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
