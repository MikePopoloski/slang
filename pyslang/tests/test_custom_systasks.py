# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

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
    # NOTE: This test reports nanobind instance leaks at interpreter shutdown
    # (Compilation, SyntaxTree, NonConstantFunction, Bag, and the Python-defined
    # BarFunc). This is a known, benign nanobind limitation, not a bug:
    #
    #   Compilation --(nb::keep_alive<1,2> on addSystemSubroutine)--> BarFunc
    #   BarFunc      --(its class -> method __closure__ -> c)-------> Compilation
    #
    # forms a reference cycle. nanobind stores keep_alive patients in a global
    # internals map (not on the instance), and its default inst_traverse only
    # visits __dict__ and the type object, so the Compilation -> BarFunc edge is
    # invisible to Python's cyclic GC; the cycle therefore survives to shutdown.
    # The keep_alive edge cannot simply be dropped: Compilation stores a raw C++
    # pointer to the subroutine, so it is required for memory safety. This mirrors
    # the documented AnalysisManager case in AnalysisBindings.cpp. The objects are
    # still correctly kept alive (no use-after-free); only their cleanup is
    # deferred to interpreter shutdown.
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
