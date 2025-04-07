# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pyslang

testfile = """
module m;
    real r;
    initial begin
        r = $foo("asdf");
    end

    $info("bar:%0d", $bar(42));
endmodule
"""


def test_custom_systasks():
    c = pyslang.Compilation()
    c.addSyntaxTree(pyslang.SyntaxTree.fromText(testfile))

    foo = pyslang.NonConstantFunction("$foo", c.realType, 1, [c.stringType])
    c.addSystemSubroutine(foo)

    class BarFunc(pyslang.SimpleSystemSubroutine):
        def __init__(self):
            pyslang.SimpleSystemSubroutine.__init__(
                self,
                "$bar",
                pyslang.SubroutineKind.Function,
                1,
                [c.intType],
                c.intType,
                False,
                False,
            )

        def eval(self, context, args, sourceRange, callInfo):
            cv = args[0].eval(context)
            if not cv:
                return cv

            return cv.value + 10

    c.addSystemSubroutine(BarFunc())

    diags = c.getAllDiagnostics()
    report = pyslang.DiagnosticEngine.reportAll(c.sourceManager, diags)
    assert (
        ("\n" + report)
        == """
source:8:5: note: $info encountered: bar:52
    $info("bar:%0d", $bar(42));
    ^
"""
    )
