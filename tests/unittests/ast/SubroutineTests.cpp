// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/statements/LoopStatements.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

TEST_CASE("Functions -- mixed param types") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo(int j, int b);
        input i;
        output logic [1:0] baz;
        baz = 2'(i);
        foo = i;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MixingSubroutinePortKinds);
}

TEST_CASE("Functions -- body params") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function automatic foo;
        input i;
        output logic [1:0] baz;
        const ref int asdf;
        logic [$bits(baz) - 2:0] i;
        baz[0] = i;
        foo = i;
    endfunction

    logic [1:0] b;
    logic j;
    int q;
    initial j = foo(1, b, q);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Functions -- body params -- port merging") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef logic[31:0] foo_t;
    function automatic foo;
        input unsigned a;
        int a;
        input signed b;
        foo_t b[3];
        ref c[1:3][4:2];
        int c[1:3][1:1];
        input d[1:2];
        int d;
        input e[1:2];
        int e[1:2][3:4];
        int e;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::SignednessNoEffect);
    CHECK(diags[1].code == diag::SignednessNoEffect);
    CHECK(diags[2].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[3].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[4].code == diag::PortDeclDimensionsMismatch);
    CHECK(diags[5].code == diag::RedefinitionDifferentType);
}

TEST_CASE("Various subroutine arg styles") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    task read(int j = 0, int k, int data = 1); endtask
    initial begin
        read(,5);
        read(2,5);
        read(,5,);
        read(,5,7);
        read(1,5,2);
    end

    function void fun(int j = 1, string s = "no"); endfunction
    initial begin
        fun(.j(2), .s("yes"));
        fun(.s("yes"));
        fun(, "yes");
        fun(.j(2));
        fun(.s("yes"), .j(2));
        fun(.s(), .j());
        fun(2);
        fun();
        fun(2, .s("yes"));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Various subroutine arg errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function void fun(int j, string s = "no"); endfunction
    initial begin
        fun(.j(0), .j(1));
        fun(.j(0), "yes");
        fun(,);
        fun(.j(), .s());
    end

    function void fun2(int j, string s); endfunction
    initial begin
        fun2(1);
        fun2(.j(1));
        fun2(1, "no", 2);
        fun2(1, .s("no"), .foo(3));
        fun2(1, "no", .j(1));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::DuplicateArgAssignment);
    CHECK(diags[1].code == diag::MixingOrderedAndNamedArgs);
    CHECK(diags[2].code == diag::ArgCannotBeEmpty);
    CHECK(diags[3].code == diag::ArgCannotBeEmpty);
    CHECK(diags[4].code == diag::TooFewArguments);
    CHECK(diags[5].code == diag::UnconnectedArg);
    CHECK(diags[6].code == diag::TooManyArguments);
    CHECK(diags[7].code == diag::ArgDoesNotExist);
    CHECK(diags[8].code == diag::DuplicateArgAssignment);
}

TEST_CASE("Function declaration") {
    auto tree = SyntaxTree::fromText(R"(
module Top;
    function static logic [15:0] foo(a, int b, output logic [15:0] u, v, inout w);
        return 16'(a + b[0]);
    endfunction
endmodule
)");

    Compilation compilation;
    const auto& instance = evalModule(tree, compilation);
    const auto& foo = instance.body.memberAt<SubroutineSymbol>(0);
    CHECK(foo.subroutineKind == SubroutineKind::Function);
    CHECK(foo.defaultLifetime == VariableLifetime::Static);
    CHECK(foo.getReturnType().getBitWidth() == 16);
    CHECK(foo.name == "foo");

    auto args = foo.getArguments();
    REQUIRE(args.size() == 5);
    CHECK(args[0]->getType().getBitWidth() == 1);
    CHECK(args[0]->direction == ArgumentDirection::In);
    CHECK(args[1]->getType().getBitWidth() == 32);
    CHECK(args[1]->direction == ArgumentDirection::In);
    CHECK(args[2]->getType().getBitWidth() == 16);
    CHECK(args[2]->direction == ArgumentDirection::Out);
    CHECK(args[3]->getType().getBitWidth() == 16);
    CHECK(args[3]->direction == ArgumentDirection::Out);
    CHECK(args[4]->getType().getBitWidth() == 1);
    CHECK(args[4]->direction == ArgumentDirection::InOut);

    const auto& returnStmt = foo.getBody().as<ReturnStatement>();
    REQUIRE(returnStmt.kind == StatementKind::Return);
    CHECK(!returnStmt.expr->bad());
    CHECK(returnStmt.expr->type->getBitWidth() == 16);

    NO_COMPILATION_ERRORS;
}

TEST_CASE("DPI Imports") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    import "DPI-C" context \begin = function void f1(input, output logic[3:0]);
    import "asdf" function void f2();
    import "DPI" function void f3();
    import "DPI-C" function void f4(ref i);
    import "DPI-C" pure function void f5(output i);
    import "DPI-C" pure function event f6(event e);
    import "DPI-C" function byte unsigned f7();

    logic [3:0] r;
    initial f1(1, r);

    import "DPI-C" function void f8(i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::ExpectedDPISpecString);
    CHECK(diags[1].code == diag::DPISpecDisallowed);
    CHECK(diags[2].code == diag::DPIRefArg);
    CHECK(diags[3].code == diag::DPIPureReturn);
    CHECK(diags[4].code == diag::DPIPureArg);
    CHECK(diags[5].code == diag::InvalidDPIReturnType);
    CHECK(diags[6].code == diag::InvalidDPIArgType);
}

TEST_CASE("DPI Exports") {
    auto tree = SyntaxTree::fromText(R"(
function bar; endfunction

module m;
    int boo;
    function foo; endfunction

    export "DPI-C" \begin = function foo;
    export "DPI" function baz;
    export "DPI-C" function boo;
    export "DPI-C" task foo;
    export "DPI-C" function bar;

    function event f1; endfunction
    function int f2(event e); endfunction

    export "DPI-C" function f1;
    export "DPI-C" function f2;
    export "DPI-C" function foo;

    function automatic void f3(ref r); endfunction
    export "DPI-C" function f3;

    import "DPI-C" function void f4;
    export "DPI-C" function f4;

    function void f5; endfunction
    export "DPI-C" \0a = function f5;

    import "DPI-C" a$ = function void f6;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 12);
    CHECK(diags[0].code == diag::DPISpecDisallowed);
    CHECK(diags[1].code == diag::TypoIdentifier);
    CHECK(diags[2].code == diag::NotASubroutine);
    CHECK(diags[3].code == diag::DPIExportKindMismatch);
    CHECK(diags[4].code == diag::DPIExportDifferentScope);
    CHECK(diags[5].code == diag::InvalidDPIReturnType);
    CHECK(diags[6].code == diag::InvalidDPIArgType);
    CHECK(diags[7].code == diag::DPIExportDuplicate);
    CHECK(diags[8].code == diag::DPIRefArg);
    CHECK(diags[9].code == diag::DPIExportImportedFunc);
    CHECK(diags[10].code == diag::InvalidDPICIdentifier);
    CHECK(diags[11].code == diag::InvalidDPICIdentifier);
}

TEST_CASE("DPI signature checking") {
    auto tree = SyntaxTree::fromText(R"(
import "DPI-C" function int foo(int a, output b);

function longint bar; endfunction
export "DPI-C" foo = function bar;

import "DPI-C" foo = function longint f1;

function int f2(int a, output b); endfunction
export "DPI-C" asdf = function f2;

module m1;
    function int f3(longint a, output b); endfunction
    export "DPI-C" asdf = function f3;
endmodule

module m2;
    function int f4(longint a, output b, input c); endfunction
    export "DPI-C" asdf = function f4;
endmodule

module m3;
    function int f5(int a, input b); endfunction
    export "DPI-C" asdf = function f5;
endmodule

module m4;
    function int asdf(int a, output b); endfunction
    export "DPI-C" function asdf;

    function int blah(int a, output b); endfunction
    export "DPI-C" asdf = function blah;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::DPISignatureMismatch);
    CHECK(diags[1].code == diag::DPISignatureMismatch);
    CHECK(diags[2].code == diag::DPISignatureMismatch);
    CHECK(diags[3].code == diag::DPISignatureMismatch);
    CHECK(diags[4].code == diag::DPISignatureMismatch);
    CHECK(diags[5].code == diag::DPIExportDuplicateCId);
}

TEST_CASE("Non-const subroutine check failures") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    import "DPI-C" function int f1(input);
    function void g; endfunction
    task t; endtask
    function int u(output o); endfunction

    if (1) begin : asdf
        function int v; endfunction
    end

    localparam int i = f1(1);
    localparam int j = f2();
    localparam int k = f3();
    localparam int l = f4();
    localparam int m = f5();

    function int f2; g(); endfunction
    function int f3; t(); endfunction
    function int f4;
        automatic logic l;
        return u(l);
    endfunction
    function int f5; return asdf.v(); endfunction

    if (t()) begin end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ConstEvalDPINotConstant);
    CHECK(diags[1].code == diag::ConstEvalVoidNotConstant);
    CHECK(diags[2].code == diag::TaskFromFunction);
    CHECK(diags[3].code == diag::ConstEvalFunctionArgDirection);
    CHECK(diags[4].code == diag::ConstEvalFunctionInsideGenerate);
    CHECK(diags[5].code == diag::ConstEvalTaskNotConstant);
}

TEST_CASE("Subroutine ref arguments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function automatic void foo;
        ref int a;
        const ref int b;
        ref int c;
    endfunction

    class C;
        int b;
    endclass

    int a;
    const C c = new;
    int d[3];
    initial begin
        foo(c.b, a, d[2]);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Subroutine ref argument errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function automatic void foo;
        ref int a;
        const ref int b;
        ref int c;
        ref int d;
        ref logic e;
    endfunction

    const int a = 1;
    localparam int b = 2;
    logic [3:0] c;

    initial begin
        foo(a, a + 2, b, c, c[0]);
    end

    function void bar;
        ref r;
    endfunction
    function void baz(ref r);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::ConstVarToRef);
    CHECK(diags[1].code == diag::InvalidRefArg);
    CHECK(diags[2].code == diag::InvalidRefArg);
    CHECK(diags[3].code == diag::RefTypeMismatch);
    CHECK(diags[4].code == diag::InvalidRefArg);
    CHECK(diags[5].code == diag::RefArgAutomaticFunc);
    CHECK(diags[6].code == diag::RefArgAutomaticFunc);
}

TEST_CASE("Subroutine return lookup location regress") {
    auto tree = SyntaxTree::fromText(R"(
module test;
    localparam w = 8;
    function [w-1:0] copy;
        input [w-1:0] w;
        begin
            copy = w;
        end
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Default lifetimes for subroutines") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo; endfunction
    initial begin : baz
        int bar;
    end
endmodule

module automatic n;
    function foo; endfunction
    initial begin : baz
        int bar;
    end
endmodule

package automatic p;
    function foo; endfunction
endpackage
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto func = [&](std::string_view name) {
        return root.lookupName<SubroutineSymbol>(name).defaultLifetime;
    };

    CHECK(func("m.foo") == VariableLifetime::Static);
    CHECK(func("n.foo") == VariableLifetime::Automatic);
    CHECK(func("p::foo") == VariableLifetime::Automatic);

    CHECK(root.lookupName<VariableSymbol>("m.baz.bar").lifetime == VariableLifetime::Static);

    auto& block = root.lookupName<StatementBlockSymbol>("n.baz");
    CHECK(block.memberAt<VariableSymbol>(0).lifetime == VariableLifetime::Automatic);
}

TEST_CASE("driver checking applied to subroutine ref args") {
    auto tree = SyntaxTree::fromText(R"(
function automatic void f(ref int a);
endfunction

function automatic void g(const ref int a);
endfunction

module m;
    int i;
    always_comb begin
        f(i);
        g(i);
    end
    always_comb begin
        f(i);
        g(i);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Subroutine referring to itself in return type") {
    auto tree = SyntaxTree::fromText(R"(
function foo foo;
endfunction

class A;
    extern function bar bar;
endclass

function bar A::bar;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::NotAType);
    CHECK(diags[1].code == diag::RecursiveDefinition);
    CHECK(diags[2].code == diag::RecursiveDefinition);
    CHECK(diags[3].code == diag::NotAType);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Extern interface method errors") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    extern task t1;
    extern forkjoin function int f1(int i);

    logic l;
    function void f2; endfunction

    modport m(input l);
    modport o(export f1);
endinterface

module n (I.m m);
    function void n.foo(int i, real r); endfunction
    function void m.foo(int i, real r); endfunction
    function void m.l(int i, real r); endfunction
    function void m.f2(); endfunction
    function void m.f1(); endfunction
endmodule

module p (I.o o);
endmodule

module q (I.o o);
    function int o.f1(int i); endfunction
endmodule

module top;
    I i();
    n n1(i);
    p p1(i);
    q q1(i);

    function int n1.foo(int i); endfunction

    real r;
    function int r.foo(int i); endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::MissingExternImpl);
    CHECK(diags[1].code == diag::ExternFuncForkJoin);
    CHECK(diags[2].code == diag::MethodReturnMismatch);
    CHECK(diags[3].code == diag::UndeclaredIdentifier);
    CHECK(diags[4].code == diag::UnknownMember);
    CHECK(diags[5].code == diag::NotASubroutine);
    CHECK(diags[6].code == diag::IfaceMethodNotExtern);
    CHECK(diags[7].code == diag::MissingExportImpl);
    CHECK(diags[8].code == diag::DupInterfaceExternMethod);
    CHECK(diags[9].code == diag::NotAnInterfaceOrPort);
    CHECK(diags[10].code == diag::NotAnInterfaceOrPort);
}

TEST_CASE("Extern iface method for iface array") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    extern function void foo(int i, real r);
    modport m(export foo);
endinterface

module n(I.m a[3]);
    initial begin
        a[0].foo(42, 3.14);
    end

    I j [3]();

    function void a.foo(int i, real r);
    endfunction

    function void j.foo(int i, real r);
    endfunction
endmodule

module m;
    I i1 [3]();
    n n1(i1);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::MissingExternImpl);
    CHECK(diags[1].code == diag::MissingExportImpl);
    CHECK(diags[2].code == diag::ExternIfaceArrayMethod);
    CHECK(diags[3].code == diag::ExternIfaceArrayMethod);
}

TEST_CASE("Function non-ansi port defaults are illegal") {
    auto tree = SyntaxTree::fromText(R"(
function foo;
    input a = 1;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SubroutinePortInitializer);
}

TEST_CASE("Function arg defaults are checked") {
    auto tree = SyntaxTree::fromText(R"(
function automatic foo(input a = baz, ref int b = 2);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::InvalidRefArg);
}

TEST_CASE("Function arg defaults with multi-driver checking") {
    auto tree = SyntaxTree::fromText(R"(
int baz, bar, biz;

function automatic void f1(output int a = baz, ref int b = bar);
endfunction

function automatic void f2(inout int c = biz);
endfunction

module m;
    initial f1();
    always_comb begin
        f1();
    end

    assign biz = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
}
