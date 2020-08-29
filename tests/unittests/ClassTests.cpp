#include "Test.h"

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
endclass
)");

    auto& diags = tree->diagnostics();
    REQUIRE(diags.size() == 17);
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
