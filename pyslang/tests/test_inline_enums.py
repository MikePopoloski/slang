# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang.ast import ASTFlags, Compilation, EnumValueSymbol, LookupLocation, Scope
from pyslang.syntax import SyntaxTree


def test_inline_enum_bindings():
    tree = SyntaxTree.fromText("""
module m;
    localparam int p = $bits(enum logic [1:0] { A, B = 2'd2 });
    logic [1:0] x;
endmodule
""")
    comp = Compilation()
    comp.addSyntaxTree(tree)
    assert not comp.getAllDiagnostics()

    # The syntax tree marks every node that has an enum somewhere beneath it.
    module = tree.root
    assert module.containsEnum
    assert module.members[0].containsEnum
    assert not module.members[1].containsEnum

    # Inline enum values are declared in the scope that contains their enum.
    body = comp.getRoot().lookupName("m").body
    b = comp.getRoot().lookupName("m.B")
    assert isinstance(b, EnumValueSymbol)
    assert b.value.value == 2
    assert b.declaringScope == Scope(body)

    # All of the values link to a single declared type that creates the enum.
    a = comp.getRoot().lookupName("m.A")
    target = b.declaredType.linkTarget
    assert target is not None
    assert target.type.isEnum
    assert a.declaredType.linkTarget.type == target.type
    assert b.type == target.type

    assert LookupLocation.sourceOrdered.index > LookupLocation.min.index
    assert ASTFlags.EnumValueType in (ASTFlags.EnumValueType | ASTFlags.LValue)
