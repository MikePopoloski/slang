import gc
from pyslang.syntax import SyntaxTree
from pyslang.ast import Compilation, SymbolKind, Lookup, ScriptSession
from pyslang.driver import Driver

def test_symbol_properties_lifetime():
    """Verify Symbol properties keep Compilation alive after parent references are dropped."""
    tree = SyntaxTree.fromText("""
module top;
    int x;
    int y;
endmodule
""")
    comp = Compilation()
    comp.addSyntaxTree(tree)
    root = comp.getRoot()
    top = root.lookupName("top")
    x_sym = top.body.lookupName("x")

    # Get properties that rely on reference_internal
    parent = x_sym.parentScope
    syntax = x_sym.syntax
    declared_type = x_sym.declaredType

    # Drop main references
    del root, top, x_sym, comp, tree
    gc.collect()

    # Accessing members of parent, syntax, declared_type must not crash or produce UAF
    assert parent is not None
    assert syntax is not None
    assert declared_type is not None

def test_expression_properties_lifetime():
    """Verify Expression child navigation keeps AST alive."""
    tree = SyntaxTree.fromText("""
module top;
    int a, b, c;
    initial a = b + c;
endmodule
""")
    comp = Compilation()
    comp.addSyntaxTree(tree)
    root = comp.getRoot()
    top = root.lookupName("top")
    
    initial_proc = None
    for member in top.body:
        if member.kind == SymbolKind.ProceduralBlock:
            initial_proc = member
            break
            
    assert initial_proc is not None
    expr_stmt = initial_proc.body
    assign_expr = expr_stmt.expr

    left_expr = assign_expr.left
    right_expr = assign_expr.right
    expr_type = assign_expr.type

    # Drop references to compilation/tree/root/proc/stmt
    del comp, tree, root, top, initial_proc, expr_stmt, assign_expr
    gc.collect()

    assert left_expr is not None
    assert right_expr is not None
    assert expr_type is not None

def test_lookup_unqualified_lifetime():
    """Verify Lookup.unqualified ties lifetime to scope argument."""
    tree = SyntaxTree.fromText("""
module top;
    int x;
endmodule
""")
    comp = Compilation()
    comp.addSyntaxTree(tree)
    root = comp.getRoot()

    top_sym = Lookup.unqualified(root, "top")

    del comp, tree, root
    gc.collect()

    assert top_sym is not None
    assert top_sym.name == "top"

def test_driver_member_fields_lifetime():
    """Verify Driver member fields keep Driver alive."""
    driver = Driver()
    sm = driver.sourceManager
    diag = driver.diagEngine
    trees = driver.syntaxTrees

    del driver
    gc.collect()

    assert sm is not None
    assert diag is not None
    assert trees is not None

def test_script_session_compilation_lifetime():
    """Verify ScriptSession.compilation keeps ScriptSession alive."""
    session = ScriptSession()
    session.eval("int a = 42;")
    comp = session.compilation

    del session
    gc.collect()

    assert comp is not None
    assert comp.getRoot() is not None

def test_compilation_builtin_types_lifetime():
    """Verify Compilation built-in types keep Compilation alive."""
    comp = Compilation()
    bit_type = comp.bitType
    logic_type = comp.logicType
    int_type = comp.intType

    del comp
    gc.collect()

    assert bit_type.isMatching(bit_type)
    assert logic_type.isMatching(logic_type)
    assert int_type.isMatching(int_type)
