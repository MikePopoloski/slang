# SPDX-FileCopyrightText: Chaitanya Sharma
# SPDX-License-Identifier: MIT

from pyslang.ast import (
    Compilation,
    MethodFlags,
    SymbolKind,
)
from pyslang.syntax import SyntaxTree


def _compile(code):
    tree, comp = SyntaxTree.fromText(code), Compilation()
    comp.addSyntaxTree(tree)
    comp.getAllDiagnostics()
    return comp


def _find_class(comp, name="Foo"):
    return next((m for cu in comp.getRoot().compilationUnits for m in cu 
                 if m.kind == SymbolKind.ClassType and m.name == name), None)


def _find_method(cls, name):
    return next((m for m in cls if m.kind == SymbolKind.Subroutine and m.name == name), None)


def test_subroutine_thisvar_class_methods():
    """Non-static class methods have thisVar pointing to the implicit `this`"""
    comp = _compile("""
    class Foo;
        int x;
        function new(int v);
            x = v;
        endfunction
        function int get_x();
            return x;
        endfunction
        task show();
            $display("%0d", x);
        endtask
    endclass
    module top; endmodule
    """)

    cls = _find_class(comp)
    assert cls is not None

    for method_name in ("new", "get_x", "show"):
        method = _find_method(cls, method_name)
        assert method is not None, f"method {method_name} not found"
        assert method.thisVar is not None, f"{method_name}.thisVar should not be None"
        assert method.thisVar.name == "this"
        assert method.thisVar.type.isClass


def test_subroutine_thisvar_static_method():
    """Static class methods have thisVar == None"""
    comp = _compile("""
    class Foo;
        static function void bar();
        endfunction
    endclass
    module top; endmodule
    """)

    method = _find_method(_find_class(comp), "bar")
    assert method is not None
    assert method.thisVar is None


def test_subroutine_thisvar_free_function():
    """Free functions have thisVar == None"""
    comp = _compile("""
    module top;
        function int add(int a, int b);
            return a + b;
        endfunction
        initial $display("%0d", add(1, 2));
    endmodule
    """)
    found = any(m.kind == SymbolKind.Subroutine and m.name == "add" and m.thisVar is None
                for inst in comp.getRoot().topInstances
                for m in inst.body)
    assert found, "free function 'add' not found"


def test_classtype_thisvar():
    comp = _compile("""
    class Foo;
        int x;
    endclass
    module top; endmodule
    """)

    cls = _find_class(comp)
    assert cls is not None
    assert cls.thisVar is not None
    assert cls.thisVar.name == "this"
    assert cls.thisVar.type.isClass


def test_subroutine_return_val_var():
    """Functions have returnValVar; tasks and void functions do not."""
    comp = _compile("""
    module top;
        function int add(int a, int b);
            return a + b;
        endfunction
        task do_nothing();
        endtask
        function void also_nothing();
        endfunction
    endmodule
    """)

    checked = set()
    for inst in comp.getRoot().topInstances:
        for m in inst.body:
            if m.kind != SymbolKind.Subroutine:
                continue
            if m.name == "add":
                assert m.returnValVar is not None
                assert m.returnValVar.name == "add"
                assert m.returnValVar.type.bitWidth == 32
                checked.add("add")
            elif m.name == "do_nothing":
                assert m.returnValVar is None
                checked.add("do_nothing")
            elif m.name == "also_nothing":
                assert m.returnValVar is None
                checked.add("also_nothing")
    assert checked == {"add", "do_nothing", "also_nothing"}, f"not all subroutines found, got: {checked}"


def test_classtype_properties():
    """ClassType.properties returns only ClassPropertySymbol members."""
    comp = _compile("""
    class Foo;
        int x;
        string s;
        real r;
        function new(); endfunction
        function int get_x(); return x; endfunction
    endclass
    module top; endmodule
    """)

    cls = _find_class(comp)
    assert cls is not None

    props = cls.properties
    assert len(props) == 3

    assert props[0].name == "x"
    assert props[0].kind == SymbolKind.ClassProperty
    assert props[0].type.isIntegral

    assert props[1].name == "s"
    assert props[1].type.isString

    assert props[2].name == "r"
    assert props[2].type.isFloating


def test_classtype_properties_with_inheritance():
    comp = _compile("""
    class Base;
        int a;
    endclass
    class Child extends Base;
        int b;
    endclass
    module top; endmodule
    """)

    cls = _find_class(comp, "Child")
    assert cls is not None

    props = cls.properties
    assert len(props) == 2
    assert props[0].name == "a", "inherited property should come first"
    assert props[1].name == "b"


def test_classtype_properties_empty():
    comp = _compile("""
    class Foo;
        function void noop(); endfunction
    endclass
    module top; endmodule
    """)

    cls = _find_class(comp)
    assert cls is not None
    assert len(cls.properties) == 0


def test_constructor_flags():
    comp = _compile("""
    class Foo;
        function new(); endfunction
    endclass
    module top; endmodule
    """)

    ctor = _find_method(_find_class(comp), "new")
    assert ctor is not None
    assert ctor.flags & MethodFlags.Constructor
