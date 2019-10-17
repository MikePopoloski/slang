#include "Test.h"

TEST_CASE("For loop statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int j, k;
    initial begin
        for (var logic f = 1, g = 0, int i = 3; i != 4; i++) begin
        end

        for (j = 2, k = 3; j != 4; j++) begin
        end
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

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
    CHECK(diags[0].code == diag::DelayNotNumeric);
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
    CHECK(diags[0].code == diag::EventExpressionConstant);
    CHECK(diags[1].code == diag::EventExpressionConstant);
    CHECK(diags[2].code == diag::ExpectedIdentifier);
    CHECK(diags[3].code == diag::InvalidEventExpression);
    CHECK(diags[4].code == diag::ExprMustBeIntegral);
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

    auto& block = compilation.getRoot().lookupName<StatementBlockSymbol>("m.block");
    auto& cs = block.getBody().as<CaseStatement>();
    CHECK(cs.expr.type->toString() == "logic[8:0]");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidCaseStmtType);
    CHECK(diags[1].code == diag::InvalidCaseStmtType);
    CHECK(diags[2].code == diag::NoCommonCaseStmtType);
    CHECK(diags[3].code == diag::NoCommonCaseStmtType);
    CHECK(diags[4].code == diag::InvalidCaseStmtType);
    CHECK(diags[5].code == diag::InvalidCaseStmtType);
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

        assert (foo);                      // not boolean
        cover (i) else $fatal(1, "SDF");   // fail stmt not allowed
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::NotBooleanConvertible);
    CHECK(diags[1].code == diag::CoverStmtNoFail);
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
    CHECK(diags[0].code == diag::ExpressionNotConstant);
}

TEST_CASE("Loop statement errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[3];
    initial begin
        repeat (foo) begin end
        repeat (-1) begin end
        while (foo) begin end
        do begin end while (foo);
        forever begin return; end
        continue;
        break;

        while (1) begin
            while (1) begin
                break;
            end
            break;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ExprMustBeIntegral);
    CHECK(diags[1].code == diag::NotBooleanConvertible);
    CHECK(diags[2].code == diag::NotBooleanConvertible);
    CHECK(diags[3].code == diag::ReturnNotInSubroutine);
    CHECK(diags[4].code == diag::StatementNotInLoop);
    CHECK(diags[5].code == diag::StatementNotInLoop);
}

TEST_CASE("Loop statement constexpr errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int foo;
    function int func1();
        repeat (-1) begin
        end
        return 1;
    endfunction

    function int func2();
        repeat (foo) begin
        end
        return 1;
    endfunction

    function int func3();
        while (foo) begin
        end
        return 1;
    endfunction

    function int func4();
        do begin end while (foo);
        return 1;
    endfunction

    localparam int p1 = func1();
    localparam int p2 = func2();
    localparam int p3 = func3();
    localparam int p4 = func4();

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExpressionNotConstant);
    CHECK(diags[1].code == diag::ExpressionNotConstant);
    CHECK(diags[2].code == diag::ExpressionNotConstant);
    CHECK(diags[3].code == diag::ExpressionNotConstant);
}

TEST_CASE("Local statement parameter") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    always begin: asdf
        localparam i = 1;
        parameter j = 2;
        logic [i+3:j] foo = '1;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<VariableSymbol>("m.asdf.foo");
    CHECK(foo.getType().getArrayRange() == ConstantRange{4, 2});
}

TEST_CASE("If statement -- unevaluated branches -- valid") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    localparam int n = -1;
    localparam logic[1:0] foo = '0;

    int j;
    initial begin
        if (n >= 0) begin
            j = foo[n];
        end else begin
            j = 1;
        end
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("If statement -- unevaluated branches -- invalid") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    localparam int n = -1;
    localparam logic[1:0] foo = '0;

    int j;
    initial begin
        if (n >= 0) begin
            j = foo[n];
        end else begin
            j = foo[n];
        end
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::IndexValueInvalid);
}

TEST_CASE("Nonblocking assignment statement") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int j;
    initial begin
        j <= 2;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Statement labels") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int j;
    initial begin
        label1: j <= 2;
    end

    always label2: begin
    end

    initial begin
        label3: for (int i = 0; i < 3; i++) begin end
    end

    initial begin : name label5: begin end end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& m = compilation.getRoot().lookupName<ModuleInstanceSymbol>("m");
    CHECK(m.lookupName("label1"));
    CHECK(m.lookupName("label2"));
    CHECK(m.lookupName("label3"));
    CHECK(m.lookupName("name"));
    CHECK(m.lookupName<StatementBlockSymbol>("name").lookupName("label5"));
}

TEST_CASE("Statement block with label and name") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial label1: begin : label2
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::LabelAndName);
}