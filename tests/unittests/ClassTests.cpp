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
endclass
)");

    auto& diags = tree->diagnostics();
    REQUIRE(diags.size() == 13);
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
}
