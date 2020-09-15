#include "Test.h"

#include "slang/symbols/ClassSymbols.h"

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

    task issue_request( int delay );
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

TEST_CASE("Class handle expressions") {
    Compilation compilation;

    auto& scope = compilation.createScriptScope();
    auto declare = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        scope.getCompilation().addSyntaxTree(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max, BindFlags::ProceduralStatement);
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
          "enum{ERR_OVERFLOW=32'sd10,ERR_UNDERFLOW=32'sd1123}Packet::e$1");
    CHECK(typeof("p.bar") == "int");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class qualifier error checking") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    const static const int i = 4;
    protected local int j;
    const randc int l = 6;

    virtual pure function foo1;
    local extern function foo2;
    pure function foo3;
    pure local function foo4;
    virtual static function foo5; endfunction

    virtual int m;
    static automatic int n;
    static var static int o;

    const function foo5; endfunction
    static task static foo6; endtask

    static parameter int x = 4;
    import p::*;

    // This should be fine
    pure virtual protected function func1;

    // Invalid qualifiers for constructors
    static function new(); endfunction
    virtual function new(); endfunction

    // Qualifiers on out-of-block decl
    static function foo::bar(); endfunction

    // Scoped name for prototype.
    extern function foo::baz();
endclass

static function C::bar();
endfunction
)");

    auto& diags = tree->diagnostics();
    REQUIRE(diags.size() == 20);
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
    CHECK(diags[18].code == diag::MethodPrototypeScoped);
    CHECK(diags[19].code == diag::QualifiersOnOutOfBlock);
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
    REQUIRE(diags.size() == 5);
    for (int i = 0; i < 5; i++) {
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

module m;
    C c1 = new;  // default specialization
    C #(4) c2 = new;

    D d1 = new; // error, no default

    typedef int Int;
    Int #(4) i1; // error, not a class

    localparam int p1 = C::p; // error
    localparam int p2 = C#()::p;
    localparam int p3 = D#(.r(5))::r;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m").body;
    CHECK(m.find<ParameterSymbol>("p2").getValue().integer() == 1);
    CHECK(m.find<ParameterSymbol>("p3").getValue().integer() == 5);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::NoDefaultSpecialization);
    CHECK(diags[1].code == diag::NotAGenericClass);
    CHECK(diags[2].code == diag::GenericClassScopeResolution);
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

// TODO: return type should be required to be scoped
function T G::foo;
    return 0;
endfunction

module m;
    G #(real) g1;
    G #(int) g2;

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
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::MethodReturnMismatch);
    CHECK(diags[1].code == diag::MethodArgCountMismatch);
    CHECK(diags[2].code == diag::MethodArgNameMismatch);
    CHECK(diags[3].code == diag::MethodArgTypeMismatch);
    CHECK(diags[4].code == diag::MethodArgNoDefault);
    CHECK(diags[5].code == diag::MethodArgDefaultMismatch);
    CHECK(diags[6].code == diag::MethodArgDefaultMismatch);
    CHECK(diags[7].code == diag::MethodArgTypeMismatch);
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
    auto init = f1.arguments[0]->getInitializer();
    REQUIRE(init);

    EvalContext ctx(compilation);
    CHECK(init->eval(ctx).integer() == 1);
}
