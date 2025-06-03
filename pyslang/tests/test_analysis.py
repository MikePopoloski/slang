# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import pyslang


def test_driver_analysis():
    """Test analysis of variable drivers"""

    tree = pyslang.SyntaxTree.fromText(
        """
module m;
    int i;
    always @* i = 1;
endmodule

module top;
    m m1();

    always @* m1.i = 2;
endmodule
"""
    )
    compilation = pyslang.Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    i = compilation.getRoot().lookupName("top.m1.i")

    analysisManager = pyslang.AnalysisManager()
    analysisManager.analyze(compilation)

    assert i is not None
    drivers = analysisManager.getDrivers(i)
    assert len(drivers) == 2
