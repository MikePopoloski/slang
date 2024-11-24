// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/syntax/AllSyntax.h"

static constexpr const char* PacketClass = R"(
class Packet;
    bit [3:0] command;
    bit [40:0] address;
    bit [4:0] master_id;
    integer time_requested;
    integer time_issued;
    integer status;
    typedef enum { ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;
    const integer buffer_size = 100;
    parameter int bar = 99;

    function new();
        command = 4'd0;
        address = 41'b0;
        master_id = 5'bx;
    endfunction : new

    task clean();
        command = 0; address = 0; master_id = 5'bx;
    endtask

    task issue_request( integer status );
        this.status = status;
    endtask

    function integer current_status();
        current_status = status;
    endfunction
endclass : Packet
)";

TEST_CASE("Basic class") {
    auto tree = SyntaxTree::fromText(PacketClass);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class handle expression types") {
    Compilation compilation;

    auto& scope = compilation.createScriptScope();
    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        scope.getCompilation().addSyntaxTree(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type->toString();
    };

    declare(PacketClass + "\nPacket p;"s);
    CHECK(typeof("p") == "Packet");
    CHECK(typeof("p == p") == "bit");
    CHECK(typeof("p !== p") == "bit");
    CHECK(typeof("(p = null)") == "Packet");
    CHECK(typeof("(p = p)") == "Packet");
    CHECK(typeof("1 ? p : p") == "Packet");
    CHECK(typeof("p.buffer_size") == "integer");
    CHECK(typeof("p.current_status()") == "integer");
    CHECK(typeof("p.clean") == "void");
    CHECK(typeof("p.ERR_OVERFLOW") ==
          "enum{ERR_OVERFLOW=32'sd10,ERR_UNDERFLOW=32'sd1123}Packet::PCKT_TYPE");
    CHECK(typeof("p.bar") == "int");

    declare(R"(
class A; endclass
class B extends A; endclass
class C extends B; endclass

class P extends A; endclass
class Q extends P; endclass
class R extends B; endclass

A ca;
B cb;
C cc;
P cp;
Q cq;
R cr;
)");
    CHECK(typeof("1 ? ca : cb") == "A");
    CHECK(typeof("1 ? cp : cb") == "A");
    CHECK(typeof("1 ? cq : cb") == "A");
    CHECK(typeof("1 ? cr : cb") == "B");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class qualifier error checking") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    const static const int i = 4;
    protected local int j;
    const randc int l = 6;

    virtual pure function logic foo1;
    local extern function logic foo2;
    pure function logic foo3;
    pure local function logic foo4;
    virtual static function foo5; endfunction

    pure virtual int m;
    static automatic int n;
    static var static int o;

    const function foo5; endfunction
    static task static foo6; endtask

    static parameter int x = 4;
    import p::*;

    // This should be fine
    pure virtual protected function logic func1;

    // Invalid qualifiers for constructors
    static function new(); endfunction
    virtual function new(); endfunction

    // Qualifiers on out-of-block decl
    static function foo::bar(); endfunction

    // Scoped name for prototype.
    extern function logic foo::baz();

    protected parameter int z = 4;

    pure virtual function new();
endclass

static function C::bar();
endfunction
)");

    auto& diags = tree->diagnostics();
    REQUIRE(diags.size() == 22);
    CHECK(diags[0].code == diag::DuplicateQualifier);
    CHECK(diags[1].code == diag::QualifierConflict);
    CHECK(diags[2].code == diag::QualifierConflict);
    CHECK(diags[3].code == diag::QualifierNotFirst);
    CHECK(diags[4].code == diag::QualifierNotFirst);
    CHECK(diags[5].code == diag::PureRequiresVirtual);
    CHECK(diags[6].code == diag::PureRequiresVirtual);
    CHECK(diags[7].code == diag::QualifierConflict);
    CHECK(diags[8].code == diag::InvalidPropertyQualifier);
    CHECK(diags[9].code == diag::QualifierConflict);
    CHECK(diags[10].code == diag::DuplicateQualifier);
    CHECK(diags[11].code == diag::InvalidMethodQualifier);
    CHECK(diags[12].code == diag::MethodStaticLifetime);
    CHECK(diags[13].code == diag::InvalidQualifierForMember);
    CHECK(diags[14].code == diag::NotAllowedInClass);
    CHECK(diags[15].code == diag::InvalidQualifierForConstructor);
    CHECK(diags[16].code == diag::InvalidQualifierForConstructor);
    CHECK(diags[17].code == diag::QualifiersOnOutOfBlock);
    CHECK(diags[18].code == diag::SubroutinePrototypeScoped);
    CHECK(diags[19].code == diag::InvalidQualifierForMember);
    CHECK(diags[20].code == diag::InvalidQualifierForConstructor);
    CHECK(diags[21].code == diag::QualifiersOnOutOfBlock);
}

TEST_CASE("Class typedefs") {
    auto tree = SyntaxTree::fromText(R"(
typedef class C;
module m;
    C c;
    initial c.baz = 1;
endmodule

class C;
    int baz;

    local typedef foo;
    protected typedef bar;

    typedef int foo;        // error, visibility must match
    protected typedef int bar;
endclass

class D;
endclass

typedef class D;
typedef class D;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ForwardTypedefVisibility);
}

TEST_CASE("Class instances") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int foo = 4;
    function void frob(int i);
        foo += i;
    endfunction
endclass

module m;
    initial begin
        automatic C c = new;
        c.foo = 5;
        c.frob(3);
        c = new;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Classes disallowed in constant contexts") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int foo = 4;
    function int frob(int i);
        return i + foo;
    endfunction

    parameter int p = 4;
    enum { ASDF = 5 } asdf;
endclass

module m;
    localparam C c1 = new;
    localparam int i = c1.foo;
    localparam int j = c1.frob(3);
    localparam int k = c1.p;
    localparam int l = c1.ASDF;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    for (int i = 0; i < 4; i++) {
        CHECK(diags[i].code == diag::ConstEvalClassType);
    }
}

TEST_CASE("Class constructor calls") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    function new(int i, real j); endfunction
endclass

class D;
endclass

module m;
    C c1 = new (3, 4.2);
    C c2 = new;
    D d1 = new (1);

    D d2 = D::new;
    C c3 = C::new(3, 0.42);

    typedef int I;

    D d3 = E::new();
    C c4 = c1::new();
    C c5 = I::new();

    int i = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::TooFewArguments);
    CHECK(diags[1].code == diag::TooManyArguments);
    CHECK(diags[2].code == diag::UndeclaredIdentifier);
    CHECK(diags[3].code == diag::NotAClass);
    CHECK(diags[4].code == diag::NotAClass);
    CHECK(diags[5].code == diag::NewClassTarget);
}

TEST_CASE("Copy class expressions") {
    auto tree = SyntaxTree::fromText(R"(
class C;
endclass

module m;
    C c1 = new;
    C c2 = new c1;
    C c3 = new 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CopyClassTarget);
}

TEST_CASE("Generic class names") {
    auto tree = SyntaxTree::fromText(R"(
class C #(int p = 1);
    function void foo();
        int k = C::p;
    endfunction
endclass

class D #(int q = 2, int r);
    int asdf;
    function void bar();
        D::asdf = r;
    endfunction
endclass

class E #(int s);
    int asdf = foo;
endclass

class F #(int t);
    int asdf = foo;

    function void baz();
        this.asdf = 1;
    endfunction
endclass

module m;
    C c1 = new;  // default specialization
    C #(4) c2 = new;

    D d1 = new; // error, no default

    typedef int Int;
    Int #(4) i1; // error, not a class

    localparam int p1 = C::p; // error
    localparam int p2 = C#()::p;
    localparam int p3 = D#(.r(5))::r;

    E #(5) e1;
    E #(6) e2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m").body;
    CHECK(m.find<ParameterSymbol>("p2").getValue().integer() == 1);
    CHECK(m.find<ParameterSymbol>("p3").getValue().integer() == 5);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::NoDefaultSpecialization);
    CHECK(diags[3].code == diag::NotAGenericClass);
    CHECK(diags[4].code == diag::GenericClassScopeResolution);
}

TEST_CASE("Generic class typedefs") {
    auto tree = SyntaxTree::fromText(R"(
typedef class C;
module m;
    typedef C TC;
    localparam type TD = C;

    TC c1 = new;
    TD d1 = new;

    localparam int p1 = TC::p;
    localparam int p2 = TD::p;
endmodule

class C #(int p = 1);
endclass

class D #(int p = 1);
endclass

typedef class D;
typedef class D;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Nested classes") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    static int asdf;
    static function void bar;
    endfunction

    class N;
        localparam int foo = 4;
        static int baz = asdf + 1;

        function void func;
            if (1) begin : block
                bar();
            end
        endfunction
    endclass
endclass

localparam int j = C::N::foo;

module m;
    C::N n = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Static class lookups") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int asdf;
    function void bar;
    endfunction

    static int foo = asdf;
    static function void baz;
        if (1) begin : block
            bar();
        end
    endfunction

    class N;
        static int baz = asdf + 1;
        function void func;
            if (1) begin : block
                bar();
            end
        endfunction
    endclass
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::NonStaticClassProperty);
    CHECK(diags[1].code == diag::NonStaticClassMethod);
    CHECK(diags[2].code == diag::NestedNonStaticClassProperty);
    CHECK(diags[3].code == diag::NestedNonStaticClassMethod);
}

TEST_CASE("Out-of-block declarations") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int i;
    static int j;
    extern function int foo(int bar, int baz = 1);
endclass

class D;
    extern static function real foo;
endclass

localparam int k = 5;

function int C::foo(int bar, int baz = 1);
    i = j + k + bar + baz;
endfunction

function real D::foo;
endfunction

class G #(type T);
    extern function T foo;
endclass

function G::T G::foo;
    return 0;
endfunction

class H #(int p);
    extern function int foo;
endclass

function int H::foo;
endfunction

module m;
    G #(real) g1;
    G #(int) g2 = new();

    int i = g2.foo();
    real r = D::foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Out-of-block error cases") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    extern function int f1(int bar, int baz);
    extern function int f2(int bar, int baz);
    extern function int f3(int bar, int baz);
    extern function int f4(int bar, int baz);
    extern function int f5(int bar);
    extern function int f6(int bar = 1 + 1);
    extern function int f7(int bar = 1 + 1 + 2);
    extern function int f8(output logic bar);
    extern function int f9(logic bar);
endclass

function real C::f1;
endfunction

function int C::f2;
endfunction

function int C::f3(int bar, int boz);
endfunction

function int C::f4(int bar, real baz);
endfunction

function int C::f5(int bar = 1);
endfunction

function int C::f6(int bar = 2);
endfunction

function int C::f7(int bar = 1 + 1 + 3);
endfunction

typedef int T;
class D;
    extern function void f(T x);
    typedef real T;
endclass
function void D::f(T x);
endfunction

function int E::f;
endfunction

class E;
    extern function int f;
endclass

class F;
    localparam type T = real;
    extern function T f;
endclass

function T F::f;
endfunction

function int asdf::foo;
endfunction

function int T::foo;
endfunction

function int F::baz;
endfunction

function int C::f8(logic bar);
endfunction

task C::f9(logic bar);
endtask
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 15);
    CHECK(diags[0].code == diag::MethodReturnMismatch);
    CHECK(diags[1].code == diag::MethodKindMismatch);
    CHECK(diags[2].code == diag::MethodArgCountMismatch);
    CHECK(diags[3].code == diag::MethodArgNameMismatch);
    CHECK(diags[4].code == diag::MethodArgTypeMismatch);
    CHECK(diags[5].code == diag::MethodArgNoDefault);
    CHECK(diags[6].code == diag::MethodArgDefaultMismatch);
    CHECK(diags[7].code == diag::MethodArgDefaultMismatch);
    CHECK(diags[8].code == diag::MethodArgTypeMismatch);
    CHECK(diags[9].code == diag::MemberDefinitionBeforeClass);
    CHECK(diags[10].code == diag::MethodReturnTypeScoped);
    CHECK(diags[11].code == diag::UndeclaredIdentifier);
    CHECK(diags[12].code == diag::NotAClass);
    CHECK(diags[13].code == diag::NoDeclInClass);
    CHECK(diags[14].code == diag::MethodArgDirectionMismatch);
}

TEST_CASE("Out-of-block default value") {
    auto tree = SyntaxTree::fromText(R"(
localparam int k = 1;
class C;
    extern function int f1(int bar = k);
    localparam int k = 2;
endclass

function int C::f1(int bar);
    return bar;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& C = compilation.getRoot().compilationUnits[0]->lookupName<ClassType>("C");
    auto& f1 = C.find<SubroutineSymbol>("f1");
    auto init = f1.getArguments()[0]->getDefaultValue();
    REQUIRE(init);

    EvalContext ctx(ASTContext(compilation.getRoot(), LookupLocation::max));
    CHECK(init->eval(ctx).integer() == 1);
}

TEST_CASE("This handle errors") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int asdf;
    static function f;
        this.asdf = 1;
    endfunction

    function int g;
        this = new;
    endfunction
endclass

module m;
    initial this.foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidThisHandle);
    CHECK(diags[1].code == diag::AssignmentToConstVar);
    CHECK(diags[2].code == diag::InvalidThisHandle);
}

TEST_CASE("Super handle errors") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    function new(int i); endfunction
endclass

class B extends A;
    function int g;
        super = new;
        return super.foo;
    endfunction

    function new;
        super.new(4);
    endfunction
endclass

class C;
    function void g;
        super.bar = 1;
        this.super.new();
    endfunction
endclass

module m;
    initial super.foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ExpectedToken);
    CHECK(diags[1].code == diag::UnknownClassMember);
    CHECK(diags[2].code == diag::SuperNoBase);
    CHECK(diags[3].code == diag::SuperNoBase);
    CHECK(diags[4].code == diag::InvalidSuperNew);
    CHECK(diags[5].code == diag::SuperOutsideClass);
}

TEST_CASE("super.new error checking") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    function new(int i); endfunction
endclass

class B extends A;
endclass

class C extends A(5); // ok
endclass

class D extends A(5);
    function new;
        super.new(5);
    endfunction
endclass

class E extends C(5);
endclass

class F extends A;
    function new;
        int i = 4;
        super.new(i);
        i++;
    endfunction
endclass

class G extends C();
    function new(int i = 4);
    endfunction
endclass

class H extends G;
endclass

module m;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::BaseConstructorNotCalled);
    CHECK(diags[1].code == diag::BaseConstructorDuplicate);
    CHECK(diags[2].code == diag::TooManyArguments);
}

TEST_CASE("Inheritance") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    integer i = 1;
    integer j = 2;
    function integer f();
        f = i;
    endfunction
endclass

class B extends A;
    integer i = 2;
    function void f();
        i = j;
        super.i = super.j;
        j = super.f();
        j = this.super.f();
    endfunction
endclass

class C extends B;
    function void g();
        f();
        i = j + C::j + A::f();
    endfunction
endclass

module m;
    A a = new;
    A b1 = B::new;
    B b2 = new;
    C c = new;
    integer i = b1.f();
    initial begin
        b2.f();
        a = b2;
        c.i = c.j;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Access visibility") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    local int i;
    protected int j;
    local function void bar; endfunction

    class P;
        static int pub;
    endclass
    protected typedef P PT;
endclass

class B extends A;
    static local function void frob; endfunction
    extern function logic foo;

    class N;
        function baz(B b);
            b.i = 1;
            b.j = 2;
            frob();
            bor(); // should not typo correct to an inaccessible function
        endfunction
    endclass
endclass

function B::foo;
    i = 1;
    j = 2;
    bar();
endfunction

module m;
    B b;
    initial b.bar();
    initial b.j = 2;

    int x = A::P::pub; // ok
    int y = A::PT::pub; // local typedef
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::LocalMemberAccess);
    CHECK(diags[1].code == diag::UndeclaredIdentifier);
    CHECK(diags[2].code == diag::LocalMemberAccess);
    CHECK(diags[3].code == diag::LocalMemberAccess);
    CHECK(diags[4].code == diag::LocalMemberAccess);
    CHECK(diags[5].code == diag::ProtectedMemberAccess);
    CHECK(diags[6].code == diag::ProtectedMemberAccess);
}

TEST_CASE("Constructor access visibility") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    local function new;
    endfunction

    class P;
        function bar;
            A a = new;
        endfunction
    endclass
endclass

class B extends A;
    function new;
    endfunction
endclass

class C extends A;
endclass

class D extends A;
    function new;
        super.new();
    endfunction
endclass

class E extends A();
endclass

class F;
    protected function new;
    endfunction
endclass

module m;
    A a = A::new;
    F f = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidConstructorAccess);
    CHECK(diags[1].code == diag::InvalidConstructorAccess);
    CHECK(diags[2].code == diag::InvalidConstructorAccess);
    CHECK(diags[3].code == diag::InvalidConstructorAccess);
    CHECK(diags[4].code == diag::InvalidConstructorAccess);
    CHECK(diags[5].code == diag::InvalidConstructorAccess);
}

TEST_CASE("Constant class properties") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    static const int i; // initializer required
    const int j = 1; // ok
    const int k; // ok

    function new;
        j = 2; // bad
        k = 2; // ok
    endfunction

    function void bar;
        k = 3; //bad
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::StaticConstNoInitializer);
    CHECK(diags[1].code == diag::AssignmentToConstVar);
    CHECK(diags[2].code == diag::AssignmentToConstVar);
}

TEST_CASE("Virtual method checking") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    virtual function int foo(int a, int b = 1); endfunction
    virtual function void bar(int a); endfunction
endclass

class B extends A;
endclass

class C extends B;
    function real foo(int a, int b); endfunction
endclass

class D extends B;
    function int foo(int b, int c); endfunction
endclass

class E extends B;
    function int foo(int a, int b, int c); endfunction
endclass

class F extends B;
    function int foo(int a, int b); endfunction
endclass

class G extends A;
    function void bar(int a = 1); endfunction
endclass

class H extends A;
    function void bar(real a); endfunction
endclass

class I extends A;
    function void bar(output int a); endfunction
endclass

class J extends A;
    task bar(int a); endtask
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::VirtualReturnMismatch);
    CHECK(diags[1].code == diag::VirtualArgNameMismatch);
    CHECK(diags[2].code == diag::VirtualArgCountMismatch);
    CHECK(diags[3].code == diag::VirtualArgNoDerivedDefault);
    CHECK(diags[4].code == diag::VirtualArgNoParentDefault);
    CHECK(diags[5].code == diag::VirtualArgTypeMismatch);
    CHECK(diags[6].code == diag::VirtualArgDirectionMismatch);
    CHECK(diags[7].code == diag::VirtualKindMismatch);
}

TEST_CASE("Virtual method with derived return type") {
    auto tree = SyntaxTree::fromText(R"(
typedef int T;

class C;
    virtual function C some_method(int a); endfunction
endclass

class D extends C;
    virtual function D some_method(T a); endfunction
endclass

class E #(type Y = logic) extends C;
    virtual function D some_method(Y a); endfunction
endclass

module m;
    E #() v1;
    E #(int) v2;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::VirtualArgTypeMismatch);
}

TEST_CASE("Virtual class errors") {
    auto tree = SyntaxTree::fromText(R"(
virtual class C;
endclass

module m;
    C c1;
    C c2 = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NewVirtualClass);
}

TEST_CASE("Pure virtual methods") {
    auto tree = SyntaxTree::fromText(R"(
virtual class C;
    pure virtual function int foo(int a, real b = 1.1);
endclass

module m;
    C c1;
    initial begin
        automatic int i = c1.foo(3);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Pure virtual method errors") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    pure virtual function int foo();
endclass

virtual class C;
    pure virtual function int foo(int a, real b = 1.1);
endclass

function int C::foo(int a, real b = 1.1);
endfunction

virtual class D extends C;
endclass

class E extends D;
    function int foo(int a, real b = 1.1); endfunction
endclass

class F extends D;
endclass

module m;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::PureInAbstract);
    CHECK(diags[1].code == diag::BodyForPure);
    CHECK(diags[2].code == diag::InheritFromAbstract);
}

TEST_CASE("Polymorphism example") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    virtual function void foo(); endfunction
endclass

class B extends A;
    function void foo(); endfunction
endclass

class C extends A;
    function void foo(); endfunction
endclass

module m;
    initial begin
        automatic A a[10];
        automatic B b = new;
        automatic C c = new;
        a[0] = b;
        a[1] = c;
        a[0].foo();
        a[1].foo();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Uninstantiated generic class error") {
    auto tree = SyntaxTree::fromText(R"(
class A;
endclass

class B #(type DT=int) extends A;
  localparam Max_int = {$bits(DT) - 1{1'b1}};
  localparam Min_int = {$bits(int) - $bits(DT){1'b1}};
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Protected member access") {
    auto tree = SyntaxTree::fromText(R"(
module top();
    class A;
        local int a_loc = 21;
        protected int a_prot = 22;
        int a = 23;
    endclass

    class B extends A;
        local int b_loc = 31;
        protected int b_prot = 32;
        int b = 33;
        function void fun();
            $display(b_prot);
        endfunction
    endclass

    B b;
    initial begin
        b = new;
        $display(b.b);
        b.fun();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface class qualifier error checking") {
    auto tree = SyntaxTree::fromText(R"(
interface class C;
    const int i = 4;
    class D; endclass
    interface class E; endclass

    local typedef int int_t;
    pure virtual protected function logic foo;

    function int bar(); endfunction
endclass
)");

    auto& diags = tree->diagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::NotAllowedInIfaceClass);
    CHECK(diags[1].code == diag::NotAllowedInIfaceClass);
    CHECK(diags[2].code == diag::NestedIface);
    CHECK(diags[3].code == diag::InvalidQualifierForIfaceMember);
    CHECK(diags[4].code == diag::InvalidQualifierForIfaceMember);
    CHECK(diags[5].code == diag::IfaceMethodPure);
}

TEST_CASE("Interface class basics") {
    auto tree = SyntaxTree::fromText(R"(
interface class I;
    pure virtual function void foo;
endclass

class A implements I;
    virtual function void foo; endfunction
endclass

module m;
    initial begin
        automatic A a = new;
        automatic I i = a;
        i.foo();
    end
endmodule

interface class PutImp#(type PUT_T = logic);
    pure virtual function void put(PUT_T a);
endclass

interface class GetImp#(type GET_T = logic);
    pure virtual function GET_T get();
endclass

class Fifo#(type T = logic) implements PutImp#(T), GetImp#(T);
    T myFifo [$:DEPTH-1];
    virtual function void put(T a);
        myFifo.push_back(a);
    endfunction
    virtual function T get();
        get = myFifo.pop_front();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface class errors") {
    auto tree = SyntaxTree::fromText(R"(
interface class I;
endclass

class A extends I;
endclass

class B implements A;
endclass

interface class J extends A;
endclass

module m;
    initial begin
        automatic I i = new;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExtendIfaceFromClass);
    CHECK(diags[1].code == diag::ImplementNonIface);
    CHECK(diags[2].code == diag::ExtendClassFromIface);
    CHECK(diags[3].code == diag::NewInterfaceClass);
}

TEST_CASE("Interface class name conflicts") {
    auto tree = SyntaxTree::fromText(R"(
interface class ABase;
    pure virtual function bit foo;
endclass

interface class A extends ABase;
    parameter type T1 = int;
    pure virtual function bit foo;
endclass

interface class B extends A;
    parameter int P1 = 1;
    pure virtual function bit foo;
endclass

interface class C;
    parameter type T1 = logic;
    parameter int P2 = 1;
    pure virtual function bit foo;
    pure virtual function logic bar;
endclass

interface class D extends A;
    parameter int P1 = 2;
    parameter int P2 = 1;
    pure virtual function logic foo;
endclass

interface class E extends B;
    pure virtual function logic bar;
    pure virtual function logic baz;
endclass

interface class F extends B;
    pure virtual function bit foo;
endclass

interface class G extends A, B, C, D, E, F;
    parameter int P2 = 3;
    pure virtual function logic bar;

    parameter int baz = 1;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::VirtualReturnMismatch);
    CHECK(diags[1].code == diag::IfaceNameConflict);
    CHECK(diags[2].code == diag::IfaceNameConflict);
    CHECK(diags[3].code == diag::IfaceNameConflict);
    CHECK(diags[4].code == diag::IfaceMethodHidden);
}

TEST_CASE("Interface class diamond with generics") {
    auto tree = SyntaxTree::fromText(R"(
interface class IntfBase #(type T = int);
    pure virtual function bit funcBase();
endclass

interface class IntfExt1 extends IntfBase#(bit);
    pure virtual function bit funcExt1();
endclass

interface class IntfExt2 extends IntfBase#(logic);
    pure virtual function bit funcExt2();
endclass

interface class IntfFinal extends IntfExt1, IntfExt2;
    typedef bit T; // Override the conflicting identifier name
    pure virtual function bit funcBase();
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface class partial implementation") {
    auto tree = SyntaxTree::fromText(R"(
interface class IntfClass;
    pure virtual function bit funcA();
    pure virtual function bit funcB();
endclass

virtual class ClassA implements IntfClass;
    virtual function bit funcA();
        return (1);
    endfunction
    pure virtual function bit funcB();
endclass

class ClassB extends ClassA;
    virtual function bit funcB();
        return (1);
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface class impl errors") {
    auto tree = SyntaxTree::fromText(R"(
interface class A;
    pure virtual function void foo;
endclass

interface class B extends A;
endclass

class C implements B;
    function void foo; endfunction
endclass

class D implements B;
    virtual function void foo(int i); endfunction
endclass

virtual class E implements B;
    pure virtual function void foo;
endclass

class F;
    virtual function void foo; endfunction
endclass

class G extends F implements B;
endclass

class H implements B;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::IfaceMethodNotVirtual);
    CHECK(diags[1].code == diag::VirtualArgCountMismatch);
    CHECK(diags[2].code == diag::IfaceMethodNoImpl);
}

TEST_CASE("Interface class forward decl") {
    auto tree = SyntaxTree::fromText(R"(
typedef A;
typedef interface class A;
typedef interface class B;
typedef interface class C;

module m;
    A a;
    B b;
    C c;
endmodule

interface class A;
endclass

interface class B #(parameter int i = 4);
endclass

typedef B#(4) C;
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Interface class type usage restrictions") {
    auto tree = SyntaxTree::fromText(R"(
interface class PutImp;
endclass

class Fifo1 #(type T = PutImp) implements T;
endclass

virtual class Fifo2 #(type T = PutImp) implements T;
endclass

interface class Fifo3 #(type T = PutImp) extends T;
endclass

typedef interface class IntfD;
class ClassB implements IntfD #(bit);
    virtual function bit[1:0] funcD();
    endfunction
endclass : ClassB

interface class IntfD #(type T1 = logic);
    typedef T1[1:0] T2;
    pure virtual function T2 funcD();
endclass : IntfD
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::IfaceExtendTypeParam);
    CHECK(diags[1].code == diag::IfaceExtendTypeParam);
    CHECK(diags[2].code == diag::IfaceExtendTypeParam);
    CHECK(diags[3].code == diag::IfaceExtendIncomplete);
}

TEST_CASE("Class resolution -- incomplete typedef") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef C;
    C::T x; // illegal
    typedef C::T c_t; // legal
    c_t y;
    class C;
        typedef int T;
    endclass
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ScopeIncompleteTypedef);
}

TEST_CASE("bitstreams of classes") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    logic [22:0] i;
    struct { logic l; byte b; } j;
endclass

interface class B;
endclass

class C;
    int foo[];
endclass

class D;
    event e;
endclass

localparam int ab = $bits(A);
localparam int bb = $bits(B);
localparam int cb = $bits(C);

module m;
    A a;
    B b;
    C c;
    D d;
    logic signed [ab:1] bits;

    initial begin
        bits = int'(a);
        bits = int'(b);
        bits = int'(c);
        bits = int'(d);
        d = D'(bits);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& a = compilation.getRoot().compilationUnits[0]->find<ParameterSymbol>("ab");
    CHECK(a.getValue().integer() == 32);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::BadSystemSubroutineArg);
    CHECK(diags[1].code == diag::QueryOnDynamicType);
    CHECK(diags[2].code == diag::BadConversion);
    CHECK(diags[3].code == diag::BadConversion);
    CHECK(diags[4].code == diag::BadConversion);
}

TEST_CASE("Class lookup from package") {
    auto tree = SyntaxTree::fromText(R"(
package Package;
    interface class Bar #(parameter A, B); endclass
endpackage

class Foo implements Package::Bar#(1, 2); endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Specialization within specialization") {
    auto tree = SyntaxTree::fromText(R"(
class D #(parameter type T);
    T t = 1;
endclass

class C #(parameter type T);
    T t = 1;
    typedef logic bad_t[3];
    function void foo;
        C #(real) c2;
        D #(bad_t) d1;
    endfunction
endclass

module m;
    C #(int) c1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadAssignment);
}

TEST_CASE("Inherit with out-of-band constructor") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    extern function new(int i);
endclass

class B extends A;
    function new;
    endfunction
endclass

function A::new(int i);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BaseConstructorNotCalled);
}

TEST_CASE("Virtualness from out-of-band override") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    extern virtual function void foo;
endclass

class B extends A;
    extern function void foo;
endclass

class C extends B;
    function void foo(int i); endfunction
endclass

class D extends B;
    extern function void foo(int i);
endclass

function void A::foo; endfunction
function void B::foo; endfunction
function void D::foo(int i); endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::VirtualArgCountMismatch);
    CHECK(diags[1].code == diag::VirtualArgCountMismatch);
}

TEST_CASE("Specialization inside block scope -- regression") {
    auto tree = SyntaxTree::fromText(R"(
class A #(parameter int i);
    static function int bar; return i; endfunction
endclass

class B;
    localparam int i = 1;
    static function int foo;
        return A #(i)::bar();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Method arg with default that refers to other arg") {
    auto tree = SyntaxTree::fromText(R"(
class A #(parameter int i);
    function void foo(int a, int b = a + 1);
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Return within constructor") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    function new;
        return;
    endfunction
endclass

class B;
    extern function new;
endclass

function B::new;
    return;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Rand qualifiers") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand int a;
    randc int b[3];
    randc A c;
    rand real r;

    struct { rand int i; randc logic j; } asdf;
endclass

module m;
    struct packed { rand int i; } a;
    union { rand int i; } b;
    struct { rand real i; } c;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::InvalidRandType);
    CHECK(diags[1].code == diag::InvalidRandType);
    CHECK(diags[2].code == diag::RandOnPackedMember);
    CHECK(diags[3].code == diag::RandOnUnionMember);
    CHECK(diags[4].code == diag::InvalidRandType);
}

TEST_CASE("Built-in class methods") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    constraint c { 1; }
    function void foo;
        c.constraint_mode(1);
    endfunction

    rand int i;
    struct { rand int i; } asdf[3];
endclass

class B;
    virtual function int randomize(); endfunction
    function int pre_randomize(); endfunction
    extern function void post_randomize(int i);
endclass

function void B::post_randomize(int i); endfunction

module m;
    A a = new;
    int i;
    string s;
    initial begin
        i = a.randomize();
        a.pre_randomize();
        a.post_randomize();
        s = a.get_randstate();
        a.set_randstate(s);
        a.srandom(1);
        a.rand_mode(1);
        a.constraint_mode(0);
        i = a.c.constraint_mode();
        a.asdf[0].i.rand_mode(1);

        // Errors
        i = a.constraint_mode(1);
        a.c.constraint_mode();
        i = a.c.constraint_mode(1);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidMethodOverride);
    CHECK(diags[1].code == diag::InvalidRandomizeOverride);
    CHECK(diags[2].code == diag::InvalidRandomizeOverride);
    CHECK(diags[3].code == diag::BadAssignment);
    CHECK(diags[4].code == diag::TooFewArguments);
    CHECK(diags[5].code == diag::TooManyArguments);
}

TEST_CASE("Constraint items") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    int i;
    rand A a;
    constraint c {
        i == 1;
        i inside {-4, 5, [3:8]};
        i >= 0 && i < 9;

        i == 'x;
        i == 3'bx;
        real'(i) == 3.1;
        3.1 == real'(i);
        a == null;
        i === 3;
    }
endclass

class B;
    rand integer x, y, z;
    constraint c1 {x inside {3, 5, [9:15], [24:32], [y:2*y], z};}

    rand integer a, b, c;
    constraint c2 {a inside {b, c};}

    integer fives[4] = '{ 5, 10, 15, 20 };
    rand integer v;
    constraint c3 { v inside {fives}; }

    constraint c4 { (a == 0) -> (b == 1); }
    constraint c5 { (a == 0) -> { b == 1; b + c == 3; } }
endclass

class C;
    rand bit [7:0] A[] ;
    constraint c1 { A.size == 5; }
    constraint c2 { A.sum() with (int'(item)) < 1000; }

    enum { big, little } mode;
    int len;
    constraint c3 {
        if (mode != big)
            if (mode == little)
                len < 10;
            else // the else applies to preceding if
                len > 100;
    }

    rand int x;
    randc int y;
    int z;
    constraint c4 {
        x dist { [100:102] :/ 1, 200 := 2, 300 := 5 };
        z + y dist { 1, 2, 3:=100 };
    }

    rand byte a[5];
    rand byte b;
    rand byte excluded;
    constraint c5 {
        unique {b, a[2:3], excluded};
        unique {a[0] + b, y, z};
        unique {a[0], x};
    }

    rand bit [7:0] arr[] ;
    constraint c6 { arr.size == 5; }
    constraint c7 { arr.sum() with (int'(item)) < 1000; }

    task t; endtask
    function void f(ref int x); endfunction

    constraint c8 { t(); f(x); }

    constraint c9 {
        disable soft x; soft x dist {5, 8};
        disable soft z;
        solve a, b, x before excluded, A;
        solve 3 before y;
        x -> { solve a before b; }
    }
endclass

class D;
    int A [2][3][4];
    bit [3:0][2:1] B [5:1][4];
    constraint c1 {
        foreach (A[i, j, k]) A[i][j][k] inside {2,4,8,16};
        foreach (B[q, r, , s]) 32'(B[q][r]) inside {1,2,3};
    }

    randc int b;
    constraint c2 {
        soft b > 4;
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 18);
    CHECK(diags[0].code == diag::UnknownConstraintLiteral);
    CHECK(diags[1].code == diag::UnknownConstraintLiteral);
    CHECK(diags[2].code == diag::InvalidConstraintExpr);
    CHECK(diags[3].code == diag::NonIntegralConstraintLiteral);
    CHECK(diags[4].code == diag::ExprNotConstraint);
    CHECK(diags[5].code == diag::RandNeededInDist);
    CHECK(diags[6].code == diag::RandCInDist);
    CHECK(diags[7].code == diag::InvalidUniquenessExpr);
    CHECK(diags[8].code == diag::RandCInUnique);
    CHECK(diags[9].code == diag::InvalidUniquenessExpr);
    CHECK(diags[10].code == diag::InequivalentUniquenessTypes);
    CHECK(diags[11].code == diag::TaskInConstraint);
    CHECK(diags[12].code == diag::OutRefFuncConstraint);
    CHECK(diags[13].code == diag::BadDisableSoft);
    CHECK(diags[14].code == diag::BadSolveBefore);
    CHECK(diags[15].code == diag::RandCInSolveBefore);
    CHECK(diags[16].code == diag::SolveBeforeDisallowed);
    CHECK(diags[17].code == diag::RandCInSoft);
}

TEST_CASE("Constraint qualifiers") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand constraint c1 { 1; }
    pure constraint c2 { 1; }

    static constraint c3 { 1; }
    constraint c4 { 1; }

    static function foo;
        c4.constraint_mode(1);
    endfunction

    rand int a;
    static constraint c5 { a > 1; }
endclass

module m;
    initial begin
        A::c3.constraint_mode(1);
        A::c4.constraint_mode(1);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InvalidConstraintQualifier);
    CHECK(diags[1].code == diag::UnexpectedConstraintBlock);
    CHECK(diags[2].code == diag::NonStaticClassProperty);
    CHECK(diags[3].code == diag::NonStaticClassProperty);
}

TEST_CASE("Class constraint block name errors") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    constraint A::B;
    constraint new { 1; }
    constraint A.B { 1; }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::ExpectedIdentifier);
    CHECK(diags[1].code == diag::NoConstraintBody);
    CHECK(diags[2].code == diag::ExpectedConstraintName);
    CHECK(diags[3].code == diag::ExpectedConstraintName);
    CHECK(diags[4].code == diag::NoDeclInClass);
}

TEST_CASE("Class constraint block out-of-band definitions") {
    auto tree = SyntaxTree::fromText(R"(
constraint A::g { 1; }

class A;
    rand int foo;
    constraint c;
    extern static constraint d;
    constraint e;                   // no impl is just a warning
    extern constraint f;            // no impl is an error
    constraint g;
    pure constraint h;
    static constraint i;
endclass

int bar;

constraint A::c { foo < bar; }
static constraint A::d { 1; }
pure constraint A::d { 1; }
constraint A::i { 1; }

virtual class B;
    pure constraint a;
    pure static constraint b;
endclass

constraint B::a { 1; }

class C extends B;
    rand int x;
    static int y;
    constraint a { this.x > y; }
    static constraint b { this.x > y; }
endclass

class D extends B;
    constraint b { 1; }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::MemberDefinitionBeforeClass);
    CHECK(diags[1].code == diag::NoConstraintBody);
    CHECK(diags[2].code == diag::NoMemberImplFound);
    CHECK(diags[3].code == diag::PureConstraintInAbstract);
    CHECK(diags[4].code == diag::ConstraintQualOutOfBlock);
    CHECK(diags[5].code == diag::Redefinition);
    CHECK(diags[6].code == diag::MismatchStaticConstraint);
    CHECK(diags[7].code == diag::BodyForPureConstraint);
    CHECK(diags[8].code == diag::InvalidThisHandle);
    CHECK(diags[9].code == diag::InheritFromAbstractConstraint);
    CHECK(diags[10].code == diag::MismatchStaticConstraint);
}

TEST_CASE("Randomize 'with' clauses") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int i;
    class Base;
        typedef int IntT;
        int bar;
        function int baz; return 1; endfunction
    endclass
    class A extends Base;
        rand int j;
        int l[5];
        function int foo; return 1; endfunction
    endclass
endpackage

module m;
    int k, l;
    p::A a;
    initial begin
        a = new;
        k = a.randomize with (j, q, foo) { j < foo() + k; };
        k = a.randomize with { j + local::l < 10; };
        k = a.randomize with (j) { j + l < 10; };
        k = a.randomize with { bar + baz(); };
    end
endmodule

int baz;

class B;
    p::A a;
    int k;
    union { int i; int j; } u;
    function void foo;
        k = a.randomize with { k + this.l < $bits(super.IntT) + $bits(this.super.IntT); };
        k = a.randomize with { k + local::this.l < 10; };
        k = a.randomize with (a.l, 1+k) { 1; };
        k = local::k; // error
        k = a.randomize (l, j);
        k = a.randomize (l, j) with (l) { l[0] > 1; };
        k = randomize (k) with { this.k < 10; };
        k = randomize (baz);
        k = randomize (k[0]);
        k = randomize (null);
        k = std::randomize(a, k) with { k < a.j; };
        k = std::randomize(a.j, u) with { k < a.j; };
        k = std::randomize(u) with { k < a.j; };
        k = std::randomize() with (a, b) { k < a.j; };
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::BadBinaryExpression);
    CHECK(diags[1].code == diag::UnknownMember);
    CHECK(diags[2].code == diag::ExpectedIdentifier);
    CHECK(diags[3].code == diag::ExpectedIdentifier);
    CHECK(diags[4].code == diag::LocalNotAllowed);
    CHECK(diags[5].code == diag::ExpectedClassPropertyName);
    CHECK(diags[6].code == diag::ExpectedClassPropertyName);
    CHECK(diags[7].code == diag::ExpectedVariableName);
    CHECK(diags[8].code == diag::InvalidRandType);
    CHECK(diags[9].code == diag::NameListWithScopeRandomize);
}

TEST_CASE("Scope randomize rand variables") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a, b;
    initial begin
        b = randomize(a) with {
            a dist { 1 :/ 1, [2:9] :/ 9};
            a inside {[1:9]};
        };
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Local members in generic classes of same type") {
    auto tree = SyntaxTree::fromText(R"(
class A #(type T = int);
    typedef A#(T) this_type;
    local T bar;

    function void foo;
        this_type tt;
        tt.bar = 1;
    endfunction
endclass

module m;
    A#(int) a1;
    A#(real) a2;
    initial begin
        a1.foo();
        a2.foo();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Speculative lookup does not default instantiate generic class") {
    auto tree = SyntaxTree::fromText(R"(
class A #(type T = event);
    local T bar = 1;
endclass

module m;
    initial begin
        A#(int) a;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface as class member") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
endinterface

class C;
    virtual I i;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Non-blocking assign to class properties") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int f;
    function foo; f <= 2; endfunction
endclass

module m;
    initial begin
        automatic C c = new;
        c.f <= 3;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class with randsequence") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int x;
    function foo;
        randsequence( main )
            main : first second third;
            first : { x = x + 10; };
            second : { if (x != 0) break; } fourth;
            third : { x = x + 10; };
            fourth : { x = x + 15; };
        endsequence
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Bit-slice of rand variable in dist constraint GH #437") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    rand bit [63:0] value;
    constraint value_c {
        value[63] dist {0 :/ 70, 1 :/ 30};
        value[0] == 1'b0;
        value[15:8] inside {
            8'h0,
            8'hF
        };
    }
    function new();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class overriding inherited enumerand") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    typedef enum { FOO, BAR } e1;
endclass

class B extends A;
    typedef enum { BAR, BAZ } e2;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Extern method default arg protected member") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    protected static int unsigned _val = 100;
    extern virtual function void set_val(int unsigned new_val = _val);
    virtual function void set_val2(int unsigned new_val = _val);
    endfunction
endclass
function void C::set_val(int unsigned new_val = _val);
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface property with qualifiers") {
    auto tree = SyntaxTree::fromText(R"(
interface intf();
endinterface
class A;
    protected virtual intf _my_intf;
    function new();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Extern task default val regress GH #475") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    extern task f(bit[7:0] i[$]='{});
endclass

task C::f(bit[7:0] i[$]='{});
endtask
)");

    // Just test no crash.
    Compilation compilation;
    compilation.addSyntaxTree(tree);
}

TEST_CASE("Select expressions in constraints can be more permissive with types") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand int min;
    rand int max;
    int name;
endclass

class C;
    int t[string];
    rand A arr[$];
    constraint tags_c {
        foreach (arr[i]) {
            arr[i].name == t["G1"] -> arr[i].min == 0 && arr[i].max == 1000;
        }
    }
    function new();
        t["G1"] = 1;
    endfunction
endclass

class D;
    string s[$];
    function void f();
        int i;
        int j = std::randomize(i) with {
            i < s.size();
        };
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("rand_mode as a function") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    rand int i;
    function void f();
        rand_mode(0);
        this.rand_mode(0);
        i.rand_mode(0);
    endfunction
endclass
module top;
    C c;
    function void make();
        c = new();
        c.rand_mode(0);
    endfunction
    initial begin
        make();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Out-of-block class method with static lifetime") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    extern task t1();
    extern task t2();
endclass
task automatic C::t1();
endtask
task static C::t2();
endtask
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MethodStaticLifetime);
}

TEST_CASE("Base class constructor checking order of inheritance") {
    auto tree = SyntaxTree::fromText(R"(
typedef class A;

class B extends A;
endclass

class Top;
    int i;
endclass

class A extends Top;
    function new();
        B b;
        b.i = 1;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Uninstantiated generic class inheritance regress GH #485") {
    auto tree = SyntaxTree::fromText(R"(
class base;
    int n;
    function void f();
        n = 0;
    endfunction
endclass

class child #(type SUPER_CLASS=base) extends SUPER_CLASS;
    function void f();
        super.f();
        n = 3;
    endfunction
endclass

module top;
endmodule

class child2 #(type SUPER_CLASS=base) extends SUPER_CLASS;
    function new();
        super.new();
    endfunction
endclass

virtual class ovm_object;
endclass

class child3 #(type SUPER_CLASS=base) extends SUPER_CLASS;
    function ovm_object create(string name="");
        child3#(SUPER_CLASS) obj = new();
        if (name != "") begin
            obj.set_name(name);
        end
        return obj;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Empty constraint set regression GH #494") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    int mode;
    rand int b;
    constraint c {
        if (mode == 0) {
            b > 2;
        } else {
            // TODO
        }
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class parameter defaults regression") {
    auto tree = SyntaxTree::fromText(R"(
class C #(type T1=int, T2=T1, parameter T1 foo = 1, parameter int bar = foo);
endclass

module m;
    C c = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class inheritance circular dependency") {
    auto tree = SyntaxTree::fromText(R"(
typedef class C;

class A extends C;
endclass

class B extends A;
endclass

class C extends B;
endclass

module m;
    C c1 = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ClassInheritanceCycle);
}

TEST_CASE("Duplicate out of block definitions") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    extern function int b();
endclass

function int A::b();
endfunction

function real A::b();
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::Redefinition);
}

TEST_CASE("Class method driver crash regress GH #552") {
    auto tree = SyntaxTree::fromText(R"(
class B;
    int v[$];
endclass

class C;
    virtual function B get();
    endfunction
    function f();
        get().v.delete();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Reversed dist range treated as empty") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    rand bit [4:0] a;
    constraint a_c {
        a dist { 16 :/ 1, [15:1] :/ 1};
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ReversedValueRange);
}

TEST_CASE("Access to static class data member with incomplete forward typedef") {
    auto tree = SyntaxTree::fromText(R"(
typedef class S;
typedef class A;

class C;
    function f();
        A a = new();
        S::a["test"] = a;
    endfunction
endclass

class S;
    static A a[string];
endclass

class A;
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Constraint in module regress") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    constraint C {}
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintNotInClass);
}

TEST_CASE("Multiple assign to static class members") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    static int foo;
endclass

function C bar;
endfunction

module m;
    C c = new;
    assign c.foo = 1;
    assign bar().foo = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Dist weight split operators") {
    auto tree = SyntaxTree::fromText(R"(
class c;
  rand int val;
  constraint cst_sum {
    val dist {1 :    = 10, 4 :   / 20};
  }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::SplitDistWeightOp);
    CHECK(diags[1].code == diag::SplitDistWeightOp);
}

TEST_CASE("Compilation error limit skips post-elab checks") {
    auto tree = SyntaxTree::fromText(R"(
class test_class#(PARA=1);
    function new();
    endfunction:new
    extern function void extern_f();
endclass

function void test_class::extern_f();
endfunction:extern_f

module top;
    initial begin
        // total 20 errors, and all of them are "use of undeclared identifier 'a'"
        a = 1; a = 1; a = 1; a = 1; a = 1;
        a = 1; a = 1; a = 1; a = 1; a = 1;
        a = 1; a = 1; a = 1; a = 1; a = 1;
        a = 1; a = 1; a = 1; a = 1; a = 1;
    end
endmodule
)");

    CompilationOptions options;
    options.errorLimit = 5;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 20);
    for (int i = 0; i < 20; i++)
        CHECK(diags[i].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Class with cycles crashes") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    A a;
    int b;
endclass

module m;
    A a = new;
    A b[2];
    int i = int'(a);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadConversion);
}

TEST_CASE("Class bistream restrictions") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    local int i;

    function void foo;
        C c = this;
        int j = int'(c);
        int k = {<<{c}};
        int l = $countones(c);
    endfunction
endclass

module m;
    C c;
    int j = int'(c);
    int k = {<<{c}};
    int l = $countones(c);
    int n = $isunknown(c);
    int o = $countbits(c, 0);
    initial begin
        c = C'(o);
        {<<{o}} = c;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[1].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[2].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[3].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[4].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[5].code == diag::ClassPrivateMembersBitstream);
    CHECK(diags[6].code == diag::ClassPrivateMembersBitstream);
}

TEST_CASE("Using this keyword in class property intializer") {
    auto tree = SyntaxTree::fromText(R"(
typedef class B;
class A;
    B b;
    function new(B b);
        this.b = b;
    endfunction
endclass

class B;
    A a1 = new(this);
    static A a2 = new(this);
endclass

class C extends B;
    A a1 = super.a1;
    static A a2 = super.a1;
    static A a3 = super.a2;
endclass

module test;
    B b = new();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidThisHandle);
    CHECK(diags[1].code == diag::NonStaticClassProperty);
    CHECK(diags[2].code == diag::NonStaticClassProperty);
}

TEST_CASE("Super handle and class randomize used from static contexts") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    static int blah;
endclass

class B extends A;
    static int i = randomize;

    static function void foo;
        int i = super.blah;
        int j = randomize;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::NonStaticClassMethod);
    CHECK(diags[1].code == diag::NonStaticClassProperty);
    CHECK(diags[2].code == diag::NonStaticClassMethod);
}

TEST_CASE("Type of this handle works") {
    auto tree = SyntaxTree::fromText(R"(
class registry #(type T=int);
    static function type(this) get();
        var static type(this) m_inst;
        if (m_inst == null)
            m_inst = new();
        return m_inst;
    endfunction
endclass

class my_int_registry extends registry #();
    function type(this) other();
    endfunction
endclass
)");

    CompilationOptions options;
    options.languageVersion = LanguageVersion::v1800_2023;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Invalid generic class handle lookup regress") {
    auto tree = SyntaxTree::fromText(R"(
class G#(t)function-G#
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just observe no crash.
    compilation.getAllDiagnostics();
}

TEST_CASE("Invalid recursive generic class specialization") {
    auto tree = SyntaxTree::fromText(R"(
class G#(G #(null) o); endclass
class H#(type a = H); endclass

module m;
    H h;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::RecursiveClassSpecialization);
    CHECK(diags[1].code == diag::RecursiveClassSpecialization);
}

TEST_CASE("Extend from final class") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class :final A;
endclass

class B extends A;
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExtendFromFinal);
}

TEST_CASE("Derived class default argument list") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class Base;
    string name;
    local int m_id;
    function new(string name, output int id);
        this.name = name;
        id = m_id++;
    endfunction : new
endclass : Base

// Class A does not add any additional arguments before the default keyword
class A extends Base;
    function new(default);
        // Compiler automatically calls super.new(default)
    endfunction : new
endclass : A

// Class B adds additional arguments before the default keyword
class B extends Base;
    int size;
    function new(int size, default);
        super.new(default); // Optional explicit use of super.new
        this.size = size;
    endfunction : new
endclass : B

// Class C adds additional arguments after the default keyword
class C extends B;
    bit enable;
    function new(default, bit enable);
        super.new(default); // Optional explicit use of super.new
        this.enable = enable; // enable is an input by default
    endfunction : new
endclass : C

module m;
    int id = 0;
    A a = new("Hello", id);
    B b = new(3, "World", id);
    C c = new(4, "!", id, 1);
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Extends clause defaulted argument list") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class Base;
    string name;
    local int m_id;
    function new(string name, output int id);
        this.name = name;
        id = m_id++;
    endfunction : new
endclass : Base

// Class A does not require an explicit constructor;
// the implicit new() method has the argument list of Base::new.
class A extends Base(default);
endclass : A

// Class B still requires an explicit constructor,
// as additional arguments are provided.
class B extends Base(default);
    int size;
    function new(int size, default);
        // Implicit call to super.new(default) from Base(default)
        this.size = size;
    endfunction : new
endclass : B

module m;
    int id = 0;
    A a = new("Hello", id);
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Derived class default argument list errors") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class Base;
    string name;
    local int m_id;
    function new(string name, output int id);
        this.name = name;
        id = m_id++;
    endfunction : new
endclass : Base

class A extends Base;
    function new(default, int i, default);
    endfunction
endclass

class B;
    function new(default);
    endfunction
endclass

class BadBase1;
    local int j;

    function new(int i = 1 + j);
    endfunction
endclass

class C extends BadBase1;
    function new(default);
    endfunction
endclass

class BadBase2;
    local function int bar; return 1; endfunction

    function new(int i = 1 + bar());
    endfunction
endclass

class D extends BadBase2;
    function new(default);
    endfunction
endclass

class E extends Base;
    function new(int i);
        super.new(default);
    endfunction
endclass

class F extends Base(default);
    function new;
    endfunction
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::MultipleDefaultConstructorArg);
    CHECK(diags[1].code == diag::SuperNoBase);
    CHECK(diags[2].code == diag::DefaultSuperArgLocalReference);
    CHECK(diags[3].code == diag::DefaultSuperArgLocalReference);
    CHECK(diags[4].code == diag::InvalidSuperNewDefault);
    CHECK(diags[5].code == diag::InvalidExtendsDefault);
}

TEST_CASE("Class property named 'new'") {
    auto tree = SyntaxTree::fromText(R"(
class A;
  int \new ;
endclass

module m;
  A a = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: class method override specifiers") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
virtual class base;
    function void f1(); endfunction             // non-virtual
    virtual function void f2(); endfunction     // virtual
    pure virtual function void f3();            // pure virtual
endclass : base

virtual class A extends base;
    function :initial void f1(); endfunction
    // OK: base::f1 is not a virtual method

    virtual function :extends :final void f2(); endfunction
    // OK: f2 shall not be overridden in subclasses of A

    function :final void f4(); endfunction
    // OK: f4 shall not be overridden in subclasses of A

    virtual function :extends void f5(); endfunction
    // NOT OK: f5 is not a virtual override
endclass : A

virtual class B extends A;
    virtual function :initial void f1(); endfunction
    // OK: A::f1 is not a virtual method

    virtual function void f2(); endfunction
    // NOT OK: f2 is specified final in A

    function void f4(); endfunction
    // NOT OK: A::f4 is specified final
endclass : B

class C extends base;
    function :initial void f2(); endfunction
    // NOT OK: f2 is a virtual override from base::f2

    function :initial void f3(); endfunction
    // NOT OK: f3 is a virtual override from pure virtual base::f3

    extern function :initial void f5();
    // OK: f5 is not a virtual override

    function :extends void f1(); endfunction
    // NOT OK: base::f1 is not virtual
endclass : C

function void C::f5(); endfunction
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::OverridingExtends);
    CHECK(diags[1].code == diag::OverridingFinal);
    CHECK(diags[2].code == diag::OverridingFinal);
    CHECK(diags[3].code == diag::OverridingInitial);
    CHECK(diags[4].code == diag::OverridingInitial);
    CHECK(diags[5].code == diag::OverridingExtends);
}

TEST_CASE("v1800-2023: class constraint override specifiers") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    constraint :initial a {}
    constraint :final b {}
    constraint d {}
endclass

class B extends A;
    constraint :extends a {}
    constraint :extends b {}
    constraint :extends c {}
    constraint :initial d {}
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::OverridingFinal);
    CHECK(diags[1].code == diag::OverridingExtends);
    CHECK(diags[2].code == diag::OverridingInitial);
}

TEST_CASE("v1800-2023: Interface class can be declared inside a class") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
  interface class B;
  endclass
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: Constraints with reals") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class real_constraint_c;
    const int ZSTATE = -100;
    const real VALUE_LOW = 0.70;
    const real VALUE_MIN = 1.43;
    const real VALUE_NOM = 3.30;
    const real VALUE_MAX = 3.65;

    rand real a;
    rand real b;
    string s;

    constraint a_constraint {
        a dist { ZSTATE := 5,
                 [VALUE_LOW:VALUE_MIN] :/ 1,
                 [VALUE_NOM +%- 1.0] :/ 13, // equivalent to 3.3 +/- 0.033
                 [VALUE_MIN:VALUE_MAX] :/ 1
        };
    }

    constraint b_constraint {
        (a inside {[VALUE_LOW:VALUE_MIN]}) -> b == real'(ZSTATE);
        b dist { ZSTATE := 1,
                 [VALUE_MIN:VALUE_MAX] :/ 20,
                 default :/ 1,
                 default : = 1,
                 default
        };
        s dist { "Hello" := 1 };
        solve a before b;
    }
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::CaseTypeMismatch);
    CHECK(diags[1].code == diag::IntFloatConv);
    CHECK(diags[2].code == diag::CaseTypeMismatch);
    CHECK(diags[3].code == diag::IntFloatConv);
    CHECK(diags[4].code == diag::MultipleDefaultDistWeight);
    CHECK(diags[5].code == diag::ExpectedToken);
    CHECK(diags[6].code == diag::SplitDistWeightOp);
    CHECK(diags[7].code == diag::ExpectedToken);
    CHECK(diags[8].code == diag::BadSetMembershipType);
}

TEST_CASE("Dist range with real values requires a weight") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand real a, b;
    constraint c {
        a dist { [a:b], [a:b] := 1};
    }
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::DistRealRangeWeight);
    CHECK(diags[1].code == diag::DistRealRangeWeight);
}

TEST_CASE("v1800-2023: Uniqueness allows real") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand real a, b;
    event c;
    constraint C {
        unique { a, b, c };
    }
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadUniquenessType);
}

TEST_CASE("v1800-2023: solve-before with reals, array sizes") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    function void foo; endfunction

    rand real a;
    rand int b[];
    constraint C {
        solve a before b.size(), b.size, foo();
    }
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::BadSolveBefore);
}

TEST_CASE("v1800-2023: disable soft with array sizes") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    rand int b[];
    constraint C {
        disable soft b.size;
        disable soft b.size();
    }
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: extern constraint blocks must match specifiers") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class A;
    extern constraint :initial a;
    extern constraint :final b;
endclass

constraint A::a {}
constraint :final A::b {}
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MismatchConstraintSpecifiers);
}

TEST_CASE("Constraint comparisons can be any type as long as no rand vars") {
    auto tree = SyntaxTree::fromText(R"(
class A;
    string a, b;
    rand int c;
    constraint C {
        if (a == b) c > 1;
        a;
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidConstraintExpr);
}

TEST_CASE("Spurious inheritance from generic param error -- GH #1058") {
    auto tree = SyntaxTree::fromText(R"(
interface class some_intf;
    pure virtual function void fn1();

    pure virtual function bit fn2();
endclass

virtual class adapter;
    function new(string name="");
    endfunction

    virtual function bit fn2();
        return 1'b1;
    endfunction

    virtual function string get_name();
        return "example";
    endfunction
endclass

virtual class used_class#(
    type extends_class = adapter
)
extends extends_class
implements some_intf;

    function new(string name="");
        super.new(name);
    endfunction

    extern virtual function void fn1();
endclass


function void used_class::fn1();
    bit the_var;
    if(get_name() == "string") begin
        the_var = 1'b1;
    end
endfunction

module top;

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unused var checking intersected with generic classes -- GH #1142") {
    auto tree = SyntaxTree::fromText(R"(
class A #(type T);
endclass

class B #(type T);
    task get((* unused *) output T t);
    endtask
endclass

class C #(type T = int);
    B #(T) b;
    (* unused *) typedef A #(C) unused;

    task test();
        T t;
        forever begin
            b.get(t);
            process(t);
        end
    endtask

    function void process((* unused *) T t);
    endfunction
endclass

module top;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class randomize can't access protected members") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    protected int a;
    rand bit b;
endclass

class T;
    function f();
        C c = new();
        int i = c.randomize() with {
            if (a == 3) {
                b == 1'b1;
            }
        };
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ProtectedMemberAccess);
}

TEST_CASE("Virtual method qualifier mismatch") {
    auto tree = SyntaxTree::fromText(R"(
class C1;
    virtual protected function void f();
    endfunction
endclass

class C2 extends C1;
    virtual function void f();
    endfunction
endclass

module top;
    C2 c;
    initial begin
        c = new();
        c.f();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::VirtualVisibilityMismatch);
}

TEST_CASE("Generic class size computation stack overflow regress") {
    auto tree = SyntaxTree::fromText(R"(
interface I;
    class G #(type l);
        G #(int) g2;
    endclass
endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}
