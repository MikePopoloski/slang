# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

from pyslang.analysis import AnalysisManager, DriverKind, FlowAnalysis
from pyslang.ast import (
    Compilation,
    ExpressionStatement,
    LSPUtilities,
    ProceduralBlockSymbol,
)
from pyslang.syntax import SyntaxTree


def test_driver_analysis():
    """Test analysis of variable drivers"""

    tree = SyntaxTree.fromText("""
module m;
    int i;
    always @* i = 1;
endmodule

module top;
    m m1();

    always @* m1.i = 2;
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    i = compilation.getRoot().lookupName("top.m1.i")

    analysisManager = AnalysisManager()
    analysisManager.analyze(compilation)

    assert i is not None
    drivers = analysisManager.getDrivers(i)
    assert len(drivers) == 2


def test_flow_analysis():
    """Test FlowAnalysis with callbacks"""
    tree = SyntaxTree.fromText("""
module m;
    int a, b, c;
    always_comb begin
        a = 1;
        b = a + 2;
        if (a > 0) begin
            c = b;
        end else begin
            c = 0;
        end
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
    root = compilation.getRoot()
    m = root.lookupName("m")

    proc_block = None
    for member in m.body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    assignments, var_refs, conditionals = [], [], []

    def on_assignment(expr):
        assignments.append(expr)

    def on_var_ref(expr):
        var_refs.append(expr)

    def on_conditional(stmt):
        conditionals.append(stmt)

    flow = FlowAnalysis(proc_block)
    flow.onAssignment, flow.onVariableRef, flow.onConditionalBegin = (
        on_assignment,
        on_var_ref,
        on_conditional,
    )
    flow.run(proc_block.body)
    assert len(assignments) == 4  # a = 1, b = a + 2, c = b, c = 0
    assert len(conditionals) == 1  # if (a > 0)
    assert "a" in [
        ref.symbol.name for ref in var_refs
    ], "Should reference 'a' in condition and RHS"
    assert "b" in [
        ref.symbol.name for ref in var_refs
    ], "Should reference 'b' in RHS of c=b"

    assert not flow.bad


def test_flow_analysis_with_state():
    """Test FlowAnalysis with custom state management"""
    tree = SyntaxTree.fromText("""
module m;
    int x;
    always_comb begin
        if (1) begin
            x = 1;
        end else begin
            x = 2;
        end
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    proc_block = None
    for member in compilation.getRoot().lookupName("m").body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    def create_top_state():
        return set()

    def copy_state(state):
        if state is None:
            return set()
        return set(state)

    def merge_states(state1, state2):
        s1 = state1 if state1 is not None else set()
        s2 = state2 if state2 is not None else set()
        return s1 | s2

    assigned_vars = []

    def on_assignment(expr):
        if hasattr(expr.left, "symbol"):
            assigned_vars.append(expr.left.symbol.name)

    flow = FlowAnalysis(proc_block)
    flow.createTopState = create_top_state
    flow.onStateCopy = copy_state
    flow.onBranchMerge = merge_states
    flow.onAssignment = on_assignment

    flow.run(proc_block.body)
    assert "x" in assigned_vars


def test_lsp_utilities_stringify():

    tree = SyntaxTree.fromText("""
module m;
    int arr[10];
    int x;
    always_comb begin
        arr[3] = 1;
        x = arr[5];
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    root = compilation.getRoot()
    m = root.lookupName("m")

    proc_block = None
    for member in m.body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    am = AnalysisManager()
    am.analyze(compilation)

    arr = root.lookupName("m.arr")
    drivers = am.getDrivers(arr)

    assert len(drivers) >= 1
    for driver_tuple in drivers:
        driver = driver_tuple[0]
        if driver.lsp is not None:
            lsp_str = LSPUtilities.stringifyLSP(driver.lsp, compilation)
            assert "arr" in lsp_str


def test_lsp_utilities_visit_lsps():

    tree = SyntaxTree.fromText("""
module m;
    int a, b;
    always_comb begin
        a = b + 1;
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    root = compilation.getRoot()
    m = root.lookupName("m")

    proc_block = None
    for member in m.body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    outer_body = proc_block.body
    assert outer_body is not None
    stmt = outer_body.body
    assert stmt is not None

    lsps_found = []

    def on_lsp(symbol, lsp_expr, is_lvalue):
        lsps_found.append((symbol.name, is_lvalue))

    if isinstance(stmt, ExpressionStatement):
        LSPUtilities.visitLSPs(stmt.expr, compilation, on_lsp, is_lvalue=True)

    assert "a" in {name for name, _ in lsps_found}, "Should find 'a' as lvalue"
    assert "b" in {name for name, _ in lsps_found}, "Should find 'b' as rvalue"


def test_driver_kind_enum():
    assert hasattr(DriverKind, "Procedural")
    assert hasattr(DriverKind, "Continuous")


def test_lsp_utilities_get_bounds():
    """Test LSPUtilities.getBounds returns correct bit ranges"""

    tree = SyntaxTree.fromText("""
module m;
    logic [31:0] data;
    logic [7:0] arr[4];
    always_comb begin
        data[15:8] = 8'hFF;
        arr[2] = 8'h00;
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    root = compilation.getRoot()

    am = AnalysisManager()
    am.analyze(compilation)

    data = root.lookupName("m.data")
    data_drivers = am.getDrivers(data)
    assert len(data_drivers) >= 1

    for driver_tuple in data_drivers:
        driver = driver_tuple[0]
        if driver.lsp is not None:
            # finds procedural block to get eval context
            m = root.lookupName("m")
            proc_block = None
            for member in m.body:
                if isinstance(member, ProceduralBlockSymbol):
                    proc_block = member
                    break
            assert proc_block is not None

            flow = FlowAnalysis(proc_block)
            bounds = LSPUtilities.getBounds(driver.lsp, flow.evalContext)
            # getBounds returns (lower_bound, upper_bound) for the bit range
            if bounds is not None:
                lower, upper = bounds
                assert lower == 8, f"Expected lower bound 8, got {lower}"
                assert upper == 15, f"Expected upper bound 15, got {upper}"


def test_flow_analysis_loop_callbacks():
    """Test that loop callbacks fire for various loop types"""

    tree = SyntaxTree.fromText("""
module m;
    int i, j, sum;
    int arr[10];
    always_comb begin
        sum = 0;
        for (i = 0; i < 10; i++) begin
            sum = sum + i;
        end
        j = 0;
        while (j < 5) begin
            j = j + 1;
        end
        foreach (arr[k]) begin
            arr[k] = k;
        end
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    root = compilation.getRoot()
    m = root.lookupName("m")

    proc_block = None
    for member in m.body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    loops_found = []

    def on_loop(stmt):
        loops_found.append(type(stmt).__name__)

    flow = FlowAnalysis(proc_block)
    flow.onLoopBegin = on_loop

    flow.run(proc_block.body)

    assert len(loops_found) == 3, f"Expected 3 loops, found {len(loops_found)}"
    assert "ForLoopStatement" in loops_found, "Should find for loop"
    assert "WhileLoopStatement" in loops_found, "Should find while loop"
    assert "ForeachLoopStatement" in loops_found, "Should find foreach loop"


def test_flow_analysis_empty_body():
    """Test that empty procedure body works without error"""

    tree = SyntaxTree.fromText("""
module m;
    always_comb begin
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    proc_block = None
    for member in compilation.getRoot().lookupName("m").body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    assignments = []

    def on_assignment(expr):
        assignments.append(expr)

    flow = FlowAnalysis(proc_block)
    flow.onAssignment = on_assignment
    flow.run(proc_block.body)

    assert len(assignments) == 0, "Empty body should have no assignments"
    assert not flow.bad, "Empty body should not set bad flag"


def test_flow_analysis_call_expression():
    """Test that function calls trigger the onCallExpression callback"""

    tree = SyntaxTree.fromText("""
module m;
    function int add(int a, int b);
        return a + b;
    endfunction

    int x, y, result;
    always_comb begin
        x = 5;
        y = 10;
        result = add(x, y);
    end
endmodule
""")
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()

    proc_block = None
    for member in compilation.getRoot().lookupName("m").body:
        if isinstance(member, ProceduralBlockSymbol):
            proc_block = member
            break

    assert proc_block is not None

    calls_found = []

    def on_call(expr):
        if hasattr(expr, "subroutine"):
            calls_found.append(expr.subroutine.name)

    flow = FlowAnalysis(proc_block)
    flow.onCallExpression = on_call
    flow.run(proc_block.body)

    assert "add" in calls_found, f"Should find call to 'add', found: {calls_found}"
