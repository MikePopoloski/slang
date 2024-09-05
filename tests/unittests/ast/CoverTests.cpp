// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

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
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::NotBooleanConvertible);
    CHECK(diags[2].code == diag::InvalidCoverageExpr);
    CHECK(diags[3].code == diag::IntFloatConv);
    CHECK(diags[4].code == diag::ExpectedToken);
    CHECK(diags[5].code == diag::Redefinition);
    CHECK(diags[6].code == diag::NotBooleanConvertible);
    CHECK(diags[7].code == diag::InvalidCoverageExpr);
    CHECK(diags[8].code == diag::CoverCrossItems);
}

TEST_CASE("Coverpoints and cover cross name lookup") {
    auto tree = SyntaxTree::fromText(R"(
typedef int baz;
class C;
    baz foo;
    covergroup cg;
        bar: coverpoint foo;
        bax: coverpoint asdfasdf;
        cross foo, bar;
    endgroup
endclass

module m;
    C c = new;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
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

TEST_CASE("Coverage options inside class") {
    auto tree = SyntaxTree::fromText(R"(
class txn;
    covergroup cg_txn;
        option.comment = "txn cov description";
    endgroup

    function new();
        cg_txn = new();
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Coverpoint bins") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int arr[];
    const int ci = 2;
    covergroup cg1 (ref int x, ref int y, input int c, int fa2[]);
        coverpoint x {
            bins a = { [0:63],65 } iff (arr);
            ignore_bins b[4] = { [127:150],[148:191] } iff (c != 0);
            illegal_bins cbins[] = { 200,201,202 };
            wildcard bins d = { [1000:$] };
            bins e = { [$:$] };
            bins f[fa2] = { 200,201,202 };
            bins others[] = default;
            wildcard bins foo = default;
            bins bar[] = default sequence;
            ignore_bins baz = default;
            bins t[] = (1,5 => 6,7), (1 => 12[*3:4] => [3:3],4 [-> 3]),
                (1 => 3 [=2:fa2] => 6[*3+:4] => 7[*]);
            bins u[3] = (1,5 => 6,7);
            bins v = func(1);
            bins w = 1+1;
            bins mod3[] = {[c:ci]} with (item % 3 == 0);
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
    CHECK(diags[1].code == diag::ValueRangeUnbounded);
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

TEST_CASE("Covergroup in class") {
    auto tree = SyntaxTree::fromText(R"(
class xyz;
    bit [3:0] m_x;
    local int m_y;
    protected bit m_z;

    covergroup cov1 @m_z;
        coverpoint m_x;
        coverpoint m_y;
    endgroup

    function new(); cov1 = new; endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup built-in methods") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup cg (int xb, yb, ref int x, y) ;
        coverpoint x {bins xbins[] = { [0:xb] }; }
        coverpoint y {bins ybins[] = { [0:yb] }; }
    endgroup

    int a,b,c,d;
    cg cv1 = new (1,2,a,b); // cv1.x has 2 bins, cv1.y has 3 bins
    cg cv2 = new (3,6,c,d); // cv2.x has 4 bins, cv2.y has 7 bins

    int covered, total;
    real r;
    initial begin
        r = cv1.x.get_inst_coverage(covered,total); // total = 2
        r = cv1.get_inst_coverage(); // total = 5
        r = cg::x::get_coverage(covered,total); // total = 6
        r = cg::get_coverage(covered); // total = 16

        cv1.start();
        cv1.x.stop();
        cv1.set_inst_name("asdf");
        cv1.sample();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup overriding sample method") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup p_cg with function sample(bit a, int x);
        coverpoint x;
        cross x, a;
    endgroup : p_cg

    p_cg cg1 = new;

    wire clk;
    bit a;
    int b,c;
    property p1;
        int x;
        @(posedge clk)(a, x = b) ##1 (c, cg1.sample(a, x));
    endproperty : p1

    c1: cover property (p1);

    function automatic void F(int j);
        bit d;
        cg1.sample(d, j);
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup overriding sample method errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    covergroup cg1 (int x) with function sample(bit a, output int y);
        coverpoint x {
            bins b = {a} iff (a);
        }
    endgroup

    covergroup cg2 with function foo;
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CovergroupOutArg);
    CHECK(diags[1].code == diag::CoverageSampleFormal);
    CHECK(diags[2].code == diag::ExpectedSampleKeyword);
    CHECK(diags[3].code == diag::ExpectedFunctionPortList);
}

TEST_CASE("Covergroup expression errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int asdf;
    wire signed [31:0] w;
    covergroup cg1 (int a, ref int r);
        coverpoint a {
            bins b = {r, asdf, w, foo()};
        }
    endgroup

    function int foo;
        return asdf;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CoverageExprVar);
    CHECK(diags[1].code == diag::CoverageExprVar);
    CHECK(diags[2].code == diag::CoverageExprVar);
    CHECK(diags[3].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
}

TEST_CASE("Cover cross bins") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i,j;
    covergroup ct;
        coverpoint i { bins i[] = { [0:1] }; }
        coverpoint j { bins j[] = { [0:1] }; }
        x1: cross i,j;
        x2: cross i,j {
            bins i_zero = binsof(i) intersect { 0 } iff (1);
        }
    endgroup

    wire clk;
    bit [7:0] v_a, v_b;
    covergroup cg @(posedge clk);
        a: coverpoint v_a {
            bins a1 = { [0:63] };
            bins a2 = { [64:127] };
            bins a3 = { [128:191] };
            bins a4 = { [192:255] };
        }
        b: coverpoint v_b {
            bins b1 = {0};
            bins b2 = { [1:84] };
            bins b3 = { [85:169] };
            bins b4 = { [170:255] };
        }
        c : cross a, b {
            bins c1 = ! binsof(a) intersect {[100:200]};
            bins c2 = binsof(a.a2) || binsof(b.b2);
            bins c3 = binsof(a.a1) && binsof(b.b4);
        }
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Cover cross filter bin selections") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [0:7] a, b;
    parameter [0:7] mask = 127;

    covergroup cg;
        coverpoint a {
            bins low[] = {[0:127]};
            bins high = {[128:255]};
        }

        coverpoint b {
            bins two[] = b with (item % 2 == 0);
            bins three[] = b with (item % 3 == 0);
        }

        X: cross a,b {
            bins apple = X with (a+b < 257) matches 127;
            bins cherry = ( binsof(b) intersect {[0:50]}
                         && binsof(a.low) intersect {[0:50]}) with (a==b);
            bins plum = binsof(b.two) with (b > 12)
                     || binsof(a.low) with (a & b & mask);
        }
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Cover cross illegal matches expr") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [0:7] a, b;
    parameter [0:7] mask = 127;

    covergroup cg;
        coverpoint a {
            bins low[] = {[0:127]};
            bins high = {[128:255]};
        }

        coverpoint b {
            bins two[] = b with (item % 2 == 0);
            bins three[] = b with (item % 3 == 0);
        }

        X: cross a,b {
            bins apple = X matches 127;
        }
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidBinsMatches);
}

TEST_CASE("Cover cross bin set expressions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a;
    logic [7:0] b;
    covergroup cg;
        coverpoint a { bins x[] = {[0:10]}; }
        coverpoint b { bins y[] = {[0:20]}; }

        aXb : cross a, b {
            bins one = '{ '{1,2}, '{3,4}, '{5,6} } matches 5;
            bins two = '{ '{1,2}, '{3,4}, '{5,6} } matches $;
        }
    endgroup

    int c,d;
    covergroup cg2(int cg_lim);
        coverpoint c;
        coverpoint d;
        cXd : cross c, d {
            function CrossQueueType myFunc1(int f_lim);
                for (int i = 0; i < f_lim; ++i)
                    myFunc1.push_back('{i,i});
            endfunction

            bins one = myFunc1(cg_lim);
            bins two = myFunc2(unsigned'(cg_lim));

            function CrossQueueType myFunc2(logic [31:0] f_lim);
                for (logic [31:0] i = 0; i < f_lim; ++i)
                    myFunc2.push_back('{int'(2*i),int'(2*i)});
            endfunction
        }
    endgroup

    cg2 cg_inst = new(3);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: derived covergroups") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class base;
    enum {red, green, blue} color;

    covergroup g1 (bit [3:0] a) with function sample(bit b);
        option.weight = 10;
        option.per_instance = 1;
        coverpoint a;
        coverpoint b;
        c: coverpoint color;
    endgroup

    function new();
        g1 = new(3);
    endfunction
endclass

class derived extends base;
    bit d;
    covergroup extends g1;
        option.weight = 1;  // overrides the weight from base g1
                            // uses per_instance=1 from base g1
        c: coverpoint color // overrides the c coverpoint in base g1
        {
            ignore_bins ignore = {blue};
        }
        coverpoint d;       // adds new coverpoint
        cross a, d;         // crosses new coverpoint with inherited one
        q: coverpoint a[1:0];
    endgroup :g1

    function new();
        super.new();
        g1 = new(4);
        g1.sample(1);
    endfunction
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Covergroup missing base") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
class base;
    int i;
endclass

class derived extends base;
    covergroup extends i;
    endgroup

    covergroup extends a;
    endgroup
endclass
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnknownCovergroupBase);
    CHECK(diags[1].code == diag::UnknownCovergroupBase);
}

TEST_CASE("v1800-2023: covergroups with real values") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
real a, b;
parameter real ZSTATE = -100.0;
parameter int XSTATE = 100;

covergroup cg_real_value;
    cvp_a: coverpoint a {
        bins highz = {[ZSTATE+/-0.1]};
        bins x_st = {[XSTATE+%-1.0]};
        bins a1[] = {[0.75:0.85]};
        bins a2[3] = {[0.75:0.85]};
        bins a3[] = {[1.0:5.0]};
        bins a4[] = {[1.0:2.0]};
        bins a5 = {[0.1:$]};
        bins a6 = default;
    }

    cvp_b: coverpoint b {
        type_option.real_interval = 0.01;
        bins xstate = {XSTATE};
        bins b1[] = {[0.75:0.85]};
        bins b2[] = {[0.75:0.85], [0.90:0.92]};
        bins b3[] = {[0.75:0.80], 0.902};
        bins b4[] = {[0.75:0.80], 0.752};
        bins b5[] = {[0.75:0.85], [0.753+/-0.01], 0.902};
    }

    ab_cross: cross cvp_a, cvp_b {
        bins az_and_bx = binsof(cvp_a.highz) && binsof(cvp_b.xstate);
        ignore_bins others = !binsof(cvp_a.highz) || !binsof(cvp_b.xstate);
    }
endgroup
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("v1800-2023: real coverpoint errors") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
real r, q;
covergroup g;
    coverpoint r;

    coverpoint r + 1 {
        bins a[] = default;
        wildcard bins b = {[1:$]} with (item == 1.0);
        bins c = (1.0 => 2.0 => 3.0);
    }

    cross r, q;
endgroup
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::RealCoverpointBins);
    CHECK(diags[1].code == diag::RealCoverpointDefaultArray);
    CHECK(diags[2].code == diag::RealCoverpointWildcardBins);
    CHECK(diags[3].code == diag::RealCoverpointWithExpr);
    CHECK(diags[4].code == diag::RealCoverpointTransBins);
    CHECK(diags[5].code == diag::RealCoverpointImplicit);
}
