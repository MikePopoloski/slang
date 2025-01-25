# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang import *

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
    c = Compilation()
    c.addSyntaxTree(SyntaxTree.fromText(testfile))

    foo = NonConstantFunction("$foo", c.realType, 1, [c.stringType])
    c.addSystemSubroutine(foo)

    class BarFunc(SimpleSystemSubroutine):
        def __init__(self):
            SimpleSystemSubroutine.__init__(
                self,
                "$bar",
                SubroutineKind.Function,
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
    report = DiagnosticEngine.reportAll(c.sourceManager, diags)
    assert (
        ("\n" + report)
        == """
source:8:5: note: $info encountered: bar:52
    $info("bar:%0d", $bar(42));
    ^
"""
    )
