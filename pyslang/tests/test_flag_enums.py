# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import enum

from pyslang import Bag, ast, syntax

FLAG_ENUMS = [
    ast.ASTFlags,
    ast.CompilationFlags,
    ast.ConstraintBlockFlags,
    ast.EvalFlags,
    ast.IntegralFlags,
    ast.LookupFlags,
    ast.LookupResultFlags,
    ast.MethodFlags,
    ast.VariableFlags,
]


def test_bitmask_enums_are_flags():
    for flags in FLAG_ENUMS:
        assert issubclass(flags, enum.IntFlag), flags.__name__


def test_combined_compilation_flags_round_trip():
    combined = (
        ast.CompilationFlags.IgnoreUnknownModules
        | ast.CompilationFlags.AllowUseBeforeDeclare
    )
    assert isinstance(combined, ast.CompilationFlags)

    options = ast.CompilationOptions()
    options.flags = combined
    assert options.flags == combined
    assert ast.CompilationFlags.IgnoreUnknownModules in options.flags
    assert ast.CompilationFlags.AllowUseBeforeDeclare in options.flags


def test_combined_compilation_flags_take_effect():
    tree = syntax.SyntaxTree.fromText(
        "module top; foo u(); assign a = b; logic b; logic a; endmodule"
    )

    def diag_codes(flags):
        options = ast.CompilationOptions()
        options.flags = flags
        compilation = ast.Compilation(Bag([options]))
        compilation.addSyntaxTree(tree)
        return {str(d.code) for d in compilation.getAllDiagnostics()}

    assert diag_codes(ast.CompilationFlags.None_) == {
        "DiagCode(UnknownModule)",
        "DiagCode(UsedBeforeDeclared)",
    }
    combined = (
        ast.CompilationFlags.IgnoreUnknownModules
        | ast.CompilationFlags.AllowUseBeforeDeclare
    )
    assert diag_codes(combined) == set()
