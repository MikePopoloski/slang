# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import gc
import weakref

from pyslang.ast import (
    Compilation,
    NonConstantFunction,
    SimpleSystemSubroutine,
    SubroutineKind,
)
from pyslang.syntax import SyntaxTree

from pyslang import DiagnosticEngine

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


def test_custom_subroutine_is_not_leaked():
    """A registered Python subroutine must be collectable (leak regression).

    This exercises the Compilation -> subroutine -> closure -> Compilation
    reference cycle. The keep-alive references are stored in the Compilation
    instance __dict__ (nb::dynamic_attr), which is garbage-collector visible, so
    the cyclic collector can break the cycle and free the subroutine.
    """
    ref = []

    def build():
        c = Compilation()

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
                return None

        b = BarFunc()
        c.addSystemSubroutine(b)
        ref.append(weakref.ref(b))

    build()
    gc.collect()
    assert ref[0]() is None, "registered custom subroutine was leaked"
