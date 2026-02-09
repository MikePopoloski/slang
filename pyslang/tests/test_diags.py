# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang import DiagnosticEngine
from pyslang.ast import Compilation, SymbolKind
from pyslang.syntax import SyntaxTree


def test_diag_args():
    text = """
    parameter int X = pa_X::X;
    parameter int unsigned Y = X;
    """

    compilation = Compilation()
    compilation.addSyntaxTree(SyntaxTree.fromText(text=text))
    engine = DiagnosticEngine(compilation.sourceManager)
    diags = compilation.getAllDiagnostics()

    assert len(diags) == 2
    assert diags[0].args == ["pa_X"]
    assert engine.formatArg(diags[0].args[0]) == "pa_X"

    assert len(diags[1].args) == 2
    assert diags[1].args[0].kind == SymbolKind.PredefinedIntegerType
    assert engine.formatArg(diags[1].args[0]) == "'int'"
    assert engine.formatArg(diags[1].args[1]) == "'int unsigned'"
