#include "Test.h"

TEST_CASE("Covergroup data type") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup cg; endgroup

    cg c1 = null;
    cg c2 = c1;
    cg c3 = new;

    initial begin
        if (c1 == c2 || c1 == null || c1 !== null || c2 === c1) begin
        end

        if (c1) begin
            c2 = c1 ? c1 : null;
        end
    end

    int arr[cg];
    initial begin
        arr[c1] = 1;
        arr[c2] = 2;
        arr[null] = 3;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup with arguments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo;
    covergroup cg(input int a, ref int b = foo, input int c = 1); endgroup

    cg c1 = new(3);
    cg c2 = new(3, foo, 52);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup basic errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup cg(int a, output b); endgroup

    logic foo;
    cg c1 = new(3, foo);

    localparam cg c2 = new(3, foo);
    localparam int p = baz();

    function automatic int baz;
        cg c3;
        cg c4 = c3;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::CovergroupOutArg);
    CHECK(diags[1].code == diag::ConstEvalCovergroupType);
    CHECK(diags[2].code == diag::ConstEvalCovergroupType);
}

TEST_CASE("Covergroup coverage events") {
    auto tree = SyntaxTree::fromText(R"(
module n;
    function bar; endfunction
endmodule

module m;
    wire clk;

    covergroup cg1 @(clk); endgroup
    covergroup cg2 @@(begin n.bar or end baz); endgroup
    covergroup cg3 (asdf) @asdf; endgroup

    covergroup cg4 @@(begin foo); endgroup
    covergroup cg5 @@(begin clk or begin foo); endgroup

    task baz; endtask
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::InvalidBlockEventTarget);
}

TEST_CASE("Cover points") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int arr[3];
    covergroup cg1 (ref int x, ref int y, input int c);
        coverpoint x; // creates coverpoint "x" covering the formal "x"
        x: coverpoint y; // INVALID: coverpoint label "x" already exists
        b: coverpoint y; // creates coverpoint "b" covering the formal "y"

        cx: coverpoint x iff (arr); // creates coverpoint "cx" covering the formal "x"

        option.weight = c; // set weight of "cg" to value of formal "c"

        bit [7:0] d: coverpoint y[31:24]; // creates coverpoint "d" covering the
                                          // high order 8 bits of the formal "y"

        real z: coverpoint y;

        e: coverpoint x {
            option.weight = 2; // set the weight of coverpoint "e"
        }
        e.option.weight = 2; // INVALID use of "e", also syntax error

        cross x, y { // Creates implicit coverpoint "y" covering
                     // the formal "y". Then creates a cross of
                     // coverpoints "x", "y"
            option.weight = c; // set weight of cross to value of formal "c"
        }
        b: cross y, x; // INVALID: coverpoint label "b" already exists

        cross x, y iff (arr);
        cross x, arr;
        cross x;
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::NotBooleanConvertible);
    CHECK(diags[2].code == diag::NonIntegralCoverageExpr);
    CHECK(diags[3].code == diag::ExpectedToken);
    CHECK(diags[4].code == diag::Redefinition);
    CHECK(diags[5].code == diag::NotBooleanConvertible);
    CHECK(diags[6].code == diag::NonIntegralCoverageExpr);
    CHECK(diags[7].code == diag::CoverCrossItems);
}

TEST_CASE("Coverage options") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup cg1 (ref int x, ref int y, input int c);
        option.weight = c;
        type_option.foo = 1;
        option.weight = 1;
        option.comment = 3.14;
        type_option.weight = c;
    endgroup

    int a_var, b_var;
    wire clk;
    covergroup gc (int maxA, int maxB) @(posedge clk);
        a : coverpoint a_var;
        b : coverpoint b_var {
            option.weight = maxA;
            type_option.weight = 1;
        }
        c : cross a, b {
            option.weight = maxB;
            type_option.weight = 1;
        }
    endgroup

    gc g1 = new (10,20);
    initial begin
        g1.option.comment = "Here is a comment set for the instance g1";
        g1.type_option.comment = "New comment";
        gc::type_option.comment = "Here is a comment for covergroup g1";
        gc::foo = 1;
        gc::option.comment = "Invalid";

        g1.option.per_instance = 1;
        gc::type_option.strobe = 1;

        g1.a.option.weight = 3;
        g1.c.option.weight = 3;
        gc::a::type_option.weight = 1;
        gc::c::type_option.weight = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::UnknownMember);
    CHECK(diags[1].code == diag::CoverageOptionDup);
    CHECK(diags[2].code == diag::BadAssignment);
    CHECK(diags[3].code == diag::AutoFromStaticInit);
    CHECK(diags[4].code == diag::UnknownCovergroupMember);
    CHECK(diags[5].code == diag::NonStaticClassProperty);
    CHECK(diags[6].code == diag::CoverOptionImmutable);
    CHECK(diags[7].code == diag::CoverOptionImmutable);
}

TEST_CASE("Coverpoint bins") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int arr[];
    covergroup cg1 (ref int x, ref int y, input int c);
        coverpoint x {
            bins a = { [0:63],65 } iff (arr);
            ignore_bins b[4] = { [127:150],[148:191] } iff (c);
            illegal_bins c[] = { 200,201,202 };
            wildcard bins d = { [1000:$] };
            bins e = { [$:$] };
            bins f[arr] = { 200,201,202 };
            bins others[] = default;
            wildcard bins foo = default;
            bins bar[] = default sequence;
            ignore_bins baz = default;
            bins t[] = (1,5 => 6,7), (1 => 12[*3:4] => [3:3],4 [-> 3]),
                (1 => 3 [=2:arr] => 6[*3+:4] => 7[*]);
            bins u[3] = (1,5 => 6,7);
            bins v = func(1);
            bins w = 1+1;
            bins mod3[] = {[0:255]} with (item % 3 == 0);
        }

        coverpoint c {
            bins func[] = c with (item % 3 == 0);
            bins func2 = asdf with (item % 3 == 0);
        }
    endgroup

    function type(arr) func(int i);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 12);
    CHECK(diags[0].code == diag::NotBooleanConvertible);
    CHECK(diags[1].code == diag::OpenRangeUnbounded);
    CHECK(diags[2].code == diag::ExprMustBeIntegral);
    CHECK(diags[3].code == diag::CoverageBinDefaultWildcard);
    CHECK(diags[4].code == diag::CoverageBinDefSeqSize);
    CHECK(diags[5].code == diag::CoverageBinDefaultIgnore);
    CHECK(diags[6].code == diag::ExprMustBeIntegral);
    CHECK(diags[7].code == diag::InvalidRepeatRange);
    CHECK(diags[8].code == diag::ExpectedExpression);
    CHECK(diags[9].code == diag::CoverageBinTransSize);
    CHECK(diags[10].code == diag::CoverageSetType);
    CHECK(diags[11].code == diag::CoverageBinTargetName);
}
