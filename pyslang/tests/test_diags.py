# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang.ast import Compilation, SymbolKind
from pyslang.syntax import SyntaxTree

from pyslang import DiagnosticEngine, Diags


def test_diag_args():
    text = """
    localparam int X = pa_X::X;
    localparam int unsigned Y = X;
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


def test_is_enabled_anywhere():
    tree = SyntaxTree.fromText(
        """
module m;
`pragma diagnostic warn="-Wundriven-port-instance"
endmodule
"""
    )

    engine = DiagnosticEngine(tree.sourceManager)
    assert len(engine.setWarningOptions([])) == 0
    assert not engine.isEnabledAnywhere(Diags.UndrivenPortInstance)

    assert len(engine.setMappingsFromPragmas(tree.root.sourceRange.start.buffer)) == 0
    assert engine.isEnabledAnywhere(Diags.UndrivenPortInstance)

    engine.setWarningOptions(["everything"])
    assert engine.isEnabledAnywhere(Diags.PartiallyUndrivenPort)
