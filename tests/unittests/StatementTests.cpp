#include "Test.h"

TEST_CASE("Delay statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    logic foo [3];

    initial begin
        #3 i++;
        #(2.1 + i) i++;

        // Invalid
        #foo i++;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == DiagCode::DelayNotNumeric);
}

TEST_CASE("Event control statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    real r;
    struct packed { logic l; } blah;
    logic foo [3];

    always @i;
    always @(i);
    always @((++i / 2) or blah, r, (posedge blah or negedge i), edge i);

    // warning about constant expr
    localparam int param = 4;
    always @(3);
    always @(posedge param + 2 / 3);

    // following are invalid
    always @;
    always @(foo or posedge r);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == DiagCode::EventExpressionConstant);
    CHECK(diags[1].code == DiagCode::EventExpressionConstant);
    CHECK(diags[2].code == DiagCode::ExpectedIdentifier);
    CHECK(diags[3].code == DiagCode::InvalidEventExpression);
    CHECK(diags[4].code == DiagCode::InvalidEdgeEventExpression);
}

TEST_CASE("Case statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    logic foo;
    string blah;
    struct { logic l; } sp;

    always begin : block
        case (foo)
            3'd7 + 3'd7: ;
            default;
            9'd9, 9'd8: ;
        endcase
    end

    always begin
        case (sp)
            default:;
        endcase // aggregates not allowed

        case (1)
            sp: ;   // aggregates not allowed
        endcase

        case (null)
            null: ;
            1'd1: ; // not comparable
        endcase

        case (null)
            null: ;
        endcase

        case ("asdf")
            "asdf": ;
            {"a", "sd"}: ;
            blah: ;
            8'd0: ; // not comparable
        endcase

        casex (foo)
            1'bx: ;
            1'd1: ;
            default;
        endcase

        casez (3.2)
            default;
        endcase // not integral

        casez (3'b1x1)
            3.2:; // not integral
        endcase
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& block = compilation.getRoot().lookupName<SequentialBlockSymbol>("m.block");
    auto& cs = block.getBody().as<CaseStatement>();
    CHECK(cs.expr.type->toString() == "logic[8:0]");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == DiagCode::InvalidCaseStmtType);
    CHECK(diags[1].code == DiagCode::InvalidCaseStmtType);
    CHECK(diags[2].code == DiagCode::NoCommonCaseStmtType);
    CHECK(diags[3].code == DiagCode::NoCommonCaseStmtType);
    CHECK(diags[4].code == DiagCode::InvalidCaseStmtType);
    CHECK(diags[5].code == DiagCode::InvalidCaseStmtType);
}

TEST_CASE("Assertion statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    logic foo [3];

    initial begin
        assert (i > 0) i++; else i--;
        assume #0 (i < 0) else i--;
        cover final (i) i++;

        assert (foo);                   // not boolean
        cover (i) else $fatal("SDF");   // fail stmt not allowed
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == DiagCode::NotBooleanConvertible);
    CHECK(diags[1].code == DiagCode::CoverStmtNoFail);
}

TEST_CASE("Assertion at compile time") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    function int foo(int x);
        assert (x > 0) else x = 42;
        assert (x < 99);
        return x;
    endfunction

    localparam int i = foo(0);
    localparam int j = foo(100);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& i = compilation.getRoot().lookupName<ParameterSymbol>("m.i");
    CHECK(i.getValue().integer() == 42);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == DiagCode::ExpressionNotConstant);
}