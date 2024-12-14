// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/Expression.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/syntax/AllSyntax.h"

TEST_CASE("I/O system tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string foo;
    int blah[3];
    bit[7:0] q[$];

    typedef int arr_t[3];

    initial begin
        $display("asdf", , 5);
        $fdisplay(1, "asdf", , 5);
        $fmonitorb(1, "asdf", , 5);
        $fstrobeh(1, "asdf", , 5);
        $fwrite(1, "asdf", , 5);
        $swrite(foo, "asdf", , 5);
        $sformat(foo, "%d", 5);
        $readmemh("SDF", blah);
        $readmemb("SDF", blah, 3);
        $readmemh("SDF", blah, 3, 4);
        $writememh("SDF", arr_t'{1,2,3}, 3, 4);
        $sformat(foo, "%p", q);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Format string - errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int ua[3];
    string s = "%s";
    union { logic a; logic b; } foo;
    union { string a; logic b; } fuz;
    struct { logic a; logic b; } bar;
    struct { logic a; string b; } baz;

    localparam string fmt = "%3.2d";

    initial begin
        $display("asdf %s%d", , 5);
        $display("%s", foo);
        $display(ua);
        $display("%d", 3.2);
        $display("%d", ua);
        $display("%9999999999d", 3);
        $display("%3.9999999999f", 3.2);
        $display("%", 3);
        $display("%-3.2d", 3);
        $display("%3m");
        $display("%0c");
        $display("%Q", 1);
        $display("%u", s);
        $display("%u", foo);
        $display("%u", fuz);
        $display("%z", bar);
        $display("%z", baz);
        $display("%z%s");
        void'($sformatf(s, "SDF"));
        void'($sformatf("%9999999999s", "SDF"));
        void'($sformatf(fmt, s));
        void'($sformatf("%d"));
        void'($sformatf("%d", 1, 2));
        void'($sformatf("%d", 3.2));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 21);
    CHECK(diags[0].code == diag::FormatEmptyArg);
    CHECK(diags[1].code == diag::FormatMismatchedType);
    CHECK(diags[2].code == diag::FormatUnspecifiedType);
    CHECK(diags[3].code == diag::FormatRealInt);
    CHECK(diags[4].code == diag::FormatMismatchedType);
    CHECK(diags[5].code == diag::FormatSpecifierInvalidWidth);
    CHECK(diags[6].code == diag::FormatSpecifierInvalidWidth);
    CHECK(diags[7].code == diag::MissingFormatSpecifier);
    CHECK(diags[8].code == diag::FormatSpecifierNotFloat);
    CHECK(diags[9].code == diag::FormatSpecifierWidthNotAllowed);
    CHECK(diags[10].code == diag::FormatSpecifierWidthNotAllowed);
    CHECK(diags[11].code == diag::UnknownFormatSpecifier);
    CHECK(diags[12].code == diag::FormatMismatchedType);
    CHECK(diags[13].code == diag::FormatMismatchedType);
    CHECK(diags[14].code == diag::FormatMismatchedType);
    CHECK(diags[15].code == diag::FormatNoArgument);
    CHECK(diags[16].code == diag::FormatNoArgument);
    CHECK(diags[17].code == diag::FormatSpecifierInvalidWidth);
    CHECK(diags[18].code == diag::FormatNoArgument);
    CHECK(diags[19].code == diag::FormatTooManyArgs);
    CHECK(diags[20].code == diag::FormatRealInt);
}

TEST_CASE("String output task - not an lvalue error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        $swrite("SDF", "asdf %d", 5);
        $sformat("SDF", "asdf %d", 5);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
    CHECK(diags[1].code == diag::ExpressionNotAssignable);
}

TEST_CASE("Readmem error cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int bar;
    real foo[3];
    int baz[3];
    string s;
    int aa[string];

    initial begin
        $readmemb("F");
        $readmemb(3.4, "asdf");
        $readmemb(3.4, foo);
        $readmemb("asdf", foo);
        $readmemb("asdf", bar);
        $readmemb("asdf", baz, s);
        $readmemb("asdf", baz, 1, s);
        $readmemb("asdf", aa);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::TooFewArguments);
    CHECK(diags[1].code == diag::ExpressionNotAssignable);
    CHECK(diags[2].code == diag::BadSystemSubroutineArg);
    CHECK(diags[3].code == diag::BadSystemSubroutineArg);
    CHECK(diags[4].code == diag::BadSystemSubroutineArg);
    CHECK(diags[5].code == diag::BadSystemSubroutineArg);
    CHECK(diags[6].code == diag::BadSystemSubroutineArg);
    CHECK(diags[7].code == diag::QueryOnAssociativeNonIntegral);
}

TEST_CASE("Methods allowed in constant context") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum { SDF, BAR } foo;
    localparam int i = foo.num;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& i = compilation.getRoot().lookupName<ParameterSymbol>("m.i");
    CHECK(i.getValue().integer() == 2);
}

TEST_CASE("Utility system functions") {
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

    // [18.13] Constrained pseudo-random value generation
    CHECK(typeof("$urandom") == "int unsigned");
    CHECK(typeof("$urandom_range(1)") == "int unsigned");
    CHECK(typeof("$urandom_range(1, 55)") == "int unsigned");

    // [20.3] Simulation time functions
    CHECK(typeof("$time") == "time");
    CHECK(typeof("$stime") == "int unsigned");
    CHECK(typeof("$realtime") == "realtime");

    // [20.4] Timescale system tasks
    CHECK(typeof("$printtimescale") == "void");
    CHECK(typeof("$timeformat") == "void");
    CHECK(typeof("$timeformat(5, 4, \"asdf\", 10)") == "void");

    // [20.15] Probabilistic distribution functions
    CHECK(typeof("$random") == "int");

    // [20.18] Miscellaneous tasks and functions
    CHECK(typeof("$system") == "int");
    CHECK(typeof("$system(\"foo bar\")") == "int");

    // [21.3] File input/output system functions
    CHECK(typeof("$fopen(\"dsa\")") == "int");
    CHECK(typeof("$fopen(\"dsa\", \"r\")") == "int");
    CHECK(typeof("$fclose(3)") == "void");
    CHECK(typeof("$fgetc(3)") == "int");
    CHECK(typeof("$ungetc(3, 4)") == "int");
    CHECK(typeof("$ftell(3)") == "int");
    CHECK(typeof("$fseek(3, 4, 5)") == "int");
    CHECK(typeof("$rewind(3)") == "int");
    CHECK(typeof("$fflush(3)") == "void");
    CHECK(typeof("$fflush()") == "void");
    CHECK(typeof("$feof(3)") == "int");

    // [21.6] Command line input
    declare("int i;");
    CHECK(typeof("$test$plusargs(\"HELLO\")") == "int");
    CHECK(typeof("$value$plusargs(\"HELLO=%d\", i)") == "int");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Conversion system functions") {
    Compilation compilation;
    auto& scope = compilation.createScriptScope();

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(source);
        ASTContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type->toString();
    };

    CHECK(typeof("$signed(3'd4)") == "bit signed[2:0]");
    CHECK(typeof("$unsigned(3'sd4)") == "bit[2:0]");

    NO_COMPILATION_ERRORS;
}

TEST_CASE("Constant system functions with non-const arguments") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[3];
    localparam int i = $size(foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Array query functions -- errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [3:1][2:5] foo [3][][$];

    localparam int p1 = $left(foo, 4);  // fine
    localparam int p2 = $right(foo[0]); // not constant
    localparam int p3 = $left(foo, p2);
    localparam int p4 = $right(foo, p2);
    localparam int p5 = $low(foo, p2);
    localparam int p6 = $high(foo, p2);
    localparam int p7 = $increment(foo, p2);
    localparam int p8 = $size(foo, p2);

    localparam int p9 = $size(foo[0], 2);
    localparam int p10 = $size(foo[0], getIndex(2));
    localparam int p11 = $size(foo, 6);
    localparam int p12 = $size(foo, 7);
    localparam int p13 = $size(foo[0]);

    localparam int p14 = $size(foo, 1, 2);
    localparam int p15 = $size(logic);
    localparam int p16 = $size(foo, 3.4);

    typedef int asdf_t[];
    localparam int p17 = $size(asdf_t);

    function int getIndex(int i);
        return i;
    endfunction

    localparam int p18 = baz(2);

    function int baz(int j);
        int i[3][];
        return $size(i, j);
    endfunction

    localparam int asdfasdf[] = '{p2};
    localparam int p19 = boz();

    function int boz;
        automatic int i = $size(asdfasdf);
        return i;
    endfunction

    localparam int p20 = $dimensions(1, 2);
    localparam int p21 = $unpacked_dimensions(real);
    localparam int p22 = $dimensions(asdf_t);

    localparam int aa[string] = '{default: -1};
    localparam int p23 = $size(aa);

    int bb[logic[67:0]];
    integer dynindex;
    localparam string p24 = $typename($size(bb, dynindex));

    function int func3(int q);
        int cc[string];
        return $size(cc, q);
    endfunction

    localparam int p25 = func3(1);

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& p24 = compilation.getRoot().lookupName<ParameterSymbol>("m.p24");
    CHECK(p24.getValue().str() == "logic[67:0]");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 16);
    CHECK(diags[0].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[1].code == diag::DynamicDimensionIndex);
    CHECK(diags[2].code == diag::DynamicDimensionIndex);
    CHECK(diags[3].code == diag::DimensionIndexInvalid);
    CHECK(diags[4].code == diag::DimensionIndexInvalid);
    CHECK(diags[5].code == diag::ConstEvalNonConstVariable);
    CHECK(diags[6].code == diag::TooManyArguments);
    CHECK(diags[7].code == diag::BadSystemSubroutineArg);
    CHECK(diags[8].code == diag::BadSystemSubroutineArg);
    CHECK(diags[9].code == diag::QueryOnDynamicType);
    CHECK(diags[10].code == diag::DynamicDimensionIndex);
    CHECK(diags[11].code == diag::TooManyArguments);
    CHECK(diags[12].code == diag::BadSystemSubroutineArg);
    CHECK(diags[13].code == diag::QueryOnDynamicType);
    CHECK(diags[14].code == diag::QueryOnAssociativeWildcard);
    CHECK(diags[15].code == diag::QueryOnAssociativeWildcard);
}

TEST_CASE("$printtimescale, $timeunit, $timeprecision") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module j;
endmodule

module k;
    j j1();
endmodule

module m;
    k k1();

    int foo;
    initial begin
        $printtimescale(m.k1.j1); // ok
        $printtimescale(5);
        $printtimescale(m.k1.j1, 5);
        $printtimescale(foo);
        $printtimescale($root);
        $printtimescale($unit);
    end

    initial begin
        foo = $timeunit;
        foo = $timeunit(5);
        foo = $timeprecision(m.k1.j1);
        foo = $timeprecision(m.k1.j1, 5);
        foo = $timeprecision(foo);
        foo = $timeunit($root);
        foo = $timeunit($unit);
    end

endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ExpectedModuleName);
    CHECK(diags[1].code == diag::TooManyArguments);
    CHECK(diags[2].code == diag::ExpectedModuleName);
    CHECK(diags[3].code == diag::ExpectedModuleName);
    CHECK(diags[4].code == diag::TooManyArguments);
    CHECK(diags[5].code == diag::ExpectedModuleName);
}

TEST_CASE("dumpvars / dumpports") {
    auto tree = SyntaxTree::fromText(R"(
module j;
endmodule

module k;
    j j1();
endmodule

module m;
    k k1();

    int foo[];
    initial begin : asdf
        $dumpvars;
        $dumpvars(1);
        $dumpvars(1, foo, m.k1, m.k1.j1);
        $dumpvars(1, 2);
        $dumpvars(1, m.asdf);
        $dumpvars(foo);

        $dumpports;
        $dumpports(m.k1, m.k1.j1);
        $dumpports(m.k1, m.k1.j1, 5);
        $dumpports(m.k1, m.k1.j1, "asdf");
        $dumpports(, "asdf");
        $dumpports("asdf");
        $dumpports(foo);
        $dumpports(foo, "asdf");
        $dumpports(3.4);
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ExpectedModOrVarName);
    CHECK(diags[1].code == diag::ExpectedModOrVarName);
    CHECK(diags[2].code == diag::BadSystemSubroutineArg);
    CHECK(diags[3].code == diag::BadSystemSubroutineArg);
    CHECK(diags[4].code == diag::ExpectedModuleName);
    CHECK(diags[5].code == diag::BadSystemSubroutineArg);
}

TEST_CASE("assertcontrol") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[];
    initial begin : asdf
        $asserton;
        $assertpasson(3);
        $assertpassoff(4, asdf);
        $assertoff;
        $assertkill(1, m.foo); // error, not scope
        $assertfailon(foo); // error
        $assertfailoff(1, 2); // error
        $assertnonvacuouson();
        $assertvacuousoff(1, m.asdf);

        $assertcontrol(1, 2, 3, 4, m.asdf);
        $assertcontrol(); // error
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExpectedScopeOrAssert);
    CHECK(diags[1].code == diag::BadSystemSubroutineArg);
    CHECK(diags[2].code == diag::ExpectedScopeOrAssert);
    CHECK(diags[3].code == diag::TooFewArguments);
}

TEST_CASE("file i/o functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string str;
    integer i;
    int mem[4];
    real r;
    initial begin
        i = $ferror(i, str);
        i = $fgets(str, i);
        i = $fscanf(i, "%d", i);
        i = $sscanf(str, "%d", i);
        i = $fread(i, i);
        i = $fread(mem, i);
        i = $fread(mem, i, 4);
        i = $fread(mem, i, , 5);

        $ferror(1, 2, 3);
        $ferror(mem, 2);
        $ferror(1, 2);
        $ferror(1, mem);

        $fgets(1, 2, 3);
        $fgets(1, 2);
        $fgets(mem, 2);
        $fgets(i, mem);

        $fscanf(1);
        $fscanf(mem, "str");
        $sscanf(mem, "str");
        $fscanf(1, mem);

        $fread(1);
        $fread(1, 2);
        $fread(r, 1);
        $fread(i, r);
        $fread(i, i, r);
        $fread(i, i, i, r);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    CHECK(diags.size() == 18);
}

TEST_CASE("warning for skipped system tasks in constant functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int i = foo();
    function int foo();
        $exit;
        $system("sdf");
        return $system("sdf"); // error
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstSysTaskIgnored);
    CHECK(diags[1].code == diag::ConstSysTaskIgnored);
    CHECK(diags[2].code == diag::SysFuncNotConst);
}

TEST_CASE("cast task") {
    auto tree = SyntaxTree::fromText(R"(
class A;
endclass

class B extends A;
endclass

module m;
    int i;
    real r;
    int da[];
    A a;
    B b;

    initial begin
        $cast(a, b);
        if ($cast(i, r)) begin end
        $cast(i, da);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Associative array non-const methods") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i[*];
    int j[string];

    int k;
    string l;

    initial begin
        i.first(k);
        k = j.last(l);
        k = j.next(l);
        k = j.prev(l);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AssociativeWildcardNotAllowed);
}

TEST_CASE("std package lookups") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    std::process p;
    std::process::state s = std::process::RUNNING;
    process p2;
    int i = process::KILLED;
    semaphore sem = new;

    initial begin
        void'(process::self());
        p.set_randstate(p.get_randstate());
        p.srandom(1);

        sem = new(5);
        sem.get();
        i = sem.try_get(9);
        sem.put(2);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("std package error handling") {
    auto tree = SyntaxTree::fromText(R"(
package std;
endpackage

module m;
    string s;

    localparam int i = foo();
    function int foo;
        automatic std::process p = process::self();
        return 1;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::ConstEvalSubroutineNotConstant);
}

TEST_CASE("Non-const array funcs") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a[3];
    int b[$];
    initial begin
        a.shuffle();
        b.shuffle();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("std mailbox") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef mailbox #(string) s_mbox;
    string s;
    int i;

    initial begin
        automatic s_mbox sm = new;
        sm.put("hello");
        sm.get(s);
        i = sm.num;
        i = sm.try_get(s);
        i = sm.try_peek(s);
        i = sm.try_put(s);
        sm.peek("sdf");
    end

    mailbox mb2;
    initial begin
        mb2.put(3);
        mb2.put(3.14);
        mb2.put(s);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InvalidRefArg);
}

TEST_CASE("Stochastic tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i, j;
    initial begin
        $q_initialize(1, 2, 3, i);
        $q_add(1, 2, 3, i);
        $q_remove(1, 2, i, j);
        j = $q_full(1, i);
        $q_exam(1, 2, i, j);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Distribution functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int seed, j;
    initial begin
        j = $dist_uniform(seed, 1, 2);
        j = $dist_normal(seed, 1, 2);
        j = $dist_exponential(seed, 5);
        j = $dist_poisson(seed, 10);
        j = $dist_chi_square(seed, 10);
        j = $dist_t(seed, 10);
        j = $dist_erlang(seed, 10, 20);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("sdf_annotate") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string s;
    initial begin
        $sdf_annotate(s);
        $sdf_annotate("sdf", m);
        $sdf_annotate(s, m, "asdf", "test", "TOOL_CONTROL", "1.0:1.0:1.0", "FROM_MTM");
        $sdf_annotate(s, 123);
        $sdf_annotate(s, s);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExpectedModuleInstance);
    CHECK(diags[1].code == diag::ExpectedModuleInstance);
}

TEST_CASE("Tracing automatic vars") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        automatic int i;
        $monitor("%d", i);
        $fstrobe(i, i);
        $dumpvars(0, i);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::AutoVarTraced);
    CHECK(diags[1].code == diag::AutoVarTraced);
    CHECK(diags[2].code == diag::AutoVarTraced);
}

TEST_CASE("Invalid clocking argument") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk;
    wire integer i = $bits(@(posedge clk));
    wire logic j = $rose(clk, @clk strong(a));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::TimingControlNotAllowed);
    CHECK(diags[1].code == diag::UnexpectedClockingExpr);
}

TEST_CASE("Hierarchical reference in $bits") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int k = $bits(n.foo);
endmodule

module n;
    int foo;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::SysFuncHierarchicalNotAllowed);
}

TEST_CASE("Sampled value functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk;
    reg a, b;
    always @(posedge clk) begin
        a <= b & $rose(b);
        a <= b & $fell(b, @clk);
        a <= b & $changed(b, @(posedge clk));
        a <= b & $stable(b, @(posedge clk));
        a <= $sampled(b);
        a <= $past(b, , , @(posedge clk));
        a <= $past(b, 5);
        a <= $past(b, 5, a | b);
        a <= $past(b, 0);
        a <= $past_gclk(b);
        a <= $rose(s.matched);
    end

    sequence s;
        int i;
        $past(i);
    endsequence
endmodule

module n;
    wire clk;
    global clocking @(posedge clk); endclocking

    reg a, b;
    always @(posedge clk) begin
        a <= $changed_gclk(b);
        a <= $changing_gclk(b);
    end

    assert property (@clk $future_gclk(a || $rising_gclk(b)));
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::PastNumTicksInvalid);
    CHECK(diags[1].code == diag::NoGlobalClocking);
    CHECK(diags[2].code == diag::SampledValueMatched);
    CHECK(diags[3].code == diag::SampledValueLocalVar);
    CHECK(diags[4].code == diag::GlobalSampledValueAssertionExpr);
    CHECK(diags[5].code == diag::GlobalSampledValueNested);
}

TEST_CASE("Global clock sys func") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    n n1();

    wire clk;
    global clocking cb @clk; endclocking
endmodule

module n;
    int i = $global_clock;
    initial begin
        @($global_clock) i++;
    end
endmodule

module o;
    int i;
    initial begin
        @($global_clock) i++;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::GlobalClockEventExpr);
    CHECK(diags[1].code == diag::NoGlobalClocking);
}

TEST_CASE("System call output args in disallowed context") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    assign j = $ferror(i, i);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NonProceduralFuncArg);
}

TEST_CASE("Coverage system functions") {
    auto tree = SyntaxTree::fromText(R"(
`undef SV_COV_START

module A(input logic x, input logic y);
endmodule

interface Z(input logic x);
endinterface

module top;
    string modName = "A";
    string hierString = "top.a";
    string bad;
    logic x, y;

    A a(.*);
    A b(.*);
    Z z(.*);

    initial begin
        int result;
        real r;
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "A", "B"); // too many args
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, 4);        // bad type
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, modName);
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, hierString);
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "A");
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "B");
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "top.a");
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "top.b");
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "top.c");
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, top.a);
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, top.b);
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, top.c);   // bad hierarchy
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, d);       // undeclared
        result = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, z);       // not a module instance
        bad = $coverage_get_max(23, 10, "top"); // bad return type
        result = $coverage_get_max(23, 10, a);
        result = $coverage_get(23, 10, b);
        result = $coverage_merge(23, "merged_cov");
        result = $coverage_save(23, "merged_cov");
        r = $get_coverage();
        $set_coverage_db_name("coverage.db");
        $load_coverage_db("coverage.db");
    end

    initial begin
        int result;
        result = $coverage_control(0, 0, 0, $root);
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::UndefineBuiltinDirective);
    CHECK(diags[1].code == diag::TooManyArguments);
    CHECK(diags[2].code == diag::NoImplicitConversion);
    CHECK(diags[3].code == diag::CouldNotResolveHierarchicalPath);
    CHECK(diags[4].code == diag::UndeclaredIdentifier);
    CHECK(diags[5].code == diag::ExpectedModuleInstance);
    CHECK(diags[6].code == diag::NoImplicitConversion);
}

TEST_CASE("PLA system tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [0:7] mem[0:3];
    logic [0:7] in;
    logic [0:3] out;
    logic [7:0] memBadOrder1[0:3];
    logic [0:7] memBadOrder2[3:0];
    string      memString[0:3];
    logic [7:0] inBadOrder;
    logic [3:0] outBadOrder;
    int i;
    real r;
    logic a;

    initial begin
        $async$and$plane(mem, in, out);
        $sync$and$array(mem, in, out, r);         // Too many arguments
        $sync$or$array(a, in, out);               // Bad mem type
        $async$nand$plane(memString, in, out);    // Bad mem type
        $sync$nor$array(mem, i, out);             // Bad input type
        $async$and$plane(mem, in, r);             // Bad output type
        $sync$or$array(memBadOrder1, in, out);    // Bad mem bit ordering
        $async$nand$plane(memBadOrder2, in, out); // Bad mem bit ordering
        $sync$nor$array(mem, inBadOrder, out);    // Bad input bit ordering
        $async$and$plane(mem, in, outBadOrder);   // Bad output bit ordering
    end
endmodule

module async_array(a1,a2,a3,a4,a5,a6,a7,b1,b2,b3);
    input a1, a2, a3, a4, a5, a6, a7;
    output b1, b2, b3;
    logic [1:7] mem[1:3]; // memory declaration for array personality
    logic b1, b2, b3;
    initial begin
        // set up the personality from the file array.dat
        $readmemb("array.dat", mem);
        // set up an asynchronous logic array with the input
        // and output terms expressed as concatenations
        $async$and$array(mem,{a1,a2,a3,a4,a5,a6,a7},{b1,b2,b3});
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::TooManyArguments);
    CHECK(diags[1].code == diag::BadSystemSubroutineArg);
    CHECK(diags[2].code == diag::BadSystemSubroutineArg);
    CHECK(diags[3].code == diag::BadSystemSubroutineArg);
    CHECK(diags[4].code == diag::BadSystemSubroutineArg);
    CHECK(diags[5].code == diag::PlaRangeInAscendingOrder);
    CHECK(diags[6].code == diag::PlaRangeInAscendingOrder);
    CHECK(diags[7].code == diag::PlaRangeInAscendingOrder);
    CHECK(diags[8].code == diag::PlaRangeInAscendingOrder);
}

TEST_CASE("Non-standard system funcs") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo = 0;
    string s = $psprintf("%0d", foo);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NonstandardSysFunc);
}

TEST_CASE("System method lvalue requirements") {
    auto tree = SyntaxTree::fromText(R"(
typedef int bar_t[];
function automatic bar_t foo;
    bar_t i = new [3];
    return i;
endfunction

module m;
    initial begin
        foo().delete();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExpressionNotAssignable);
}

TEST_CASE("Sampled value functions with clocking in always_comb") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic clk;
    logic a, b;
    always_comb begin
        a = $past(b,,,@(posedge clk));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Assert control functions referencing instances") {
    auto tree = SyntaxTree::fromText(R"(
module M(
    input logic clk,
    input logic rst_b
);
    myprop: assert property(@(posedge clk) disable iff (rst_b) ~1);
endmodule

module top;
    logic clk;
    logic rst_b;

    M m(
        .clk   (clk),
        .rst_b (rst_b)
    );

    initial begin
        $assertoff(0, m);
        $assertoff(0, m.myprop);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("No width warning for randomize method") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    function bit f();
        bit x;
        bit rc = std::randomize(x);
        assert (rc);
        return x;
    endfunction
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Array map method") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module m;
    int A[] = {1,2,3}, B[] = {2,3,5}, C[$];
    bit Compare[];

    initial begin
        A = A.map() with (item + 1); // A = {2,3,4}
        C = A.map(a) with (a + B[a.index]); // C = {4,6,9}
        Compare = A.map(a) with (a == B[a.index]); // Compare = {1,1,0}
    end
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Array map method not allowed in 2017") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int A[] = {1,2,3};
    int B[] = A.map with (item);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::WrongLanguageVersion);
}

TEST_CASE("Assert control functions force hierarchical lookup") {
    auto tree = SyntaxTree::fromText(R"(
module top();
  m m1();
endmodule

module m();
  initial begin
    $assertoff(0, m);
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Weak References") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
module m;
    class A;
    endclass

    A a = new;
    weak_reference #(A) ref1 = new (a);
    weak_reference #(A) ref2 = new (a);

    longint l = weak_reference #(A)::get_id(a);

    initial begin
        assert(ref1 != ref2);
        assert(ref1.get() == ref2.get());

        ref1.clear();
        ref2.clear();
    end
endmodule
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Weak reference errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    weak_reference a;
    weak_reference #(int) b;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::NoDefaultSpecialization);
    CHECK(diags[1].code == diag::WrongLanguageVersion);
    CHECK(diags[2].code == diag::TypeIsNotAClass);
}

TEST_CASE("v1800-2023 clarification: severity system tasks should work in constant functions") {
    auto tree = SyntaxTree::fromText(R"(
function foo(int i);
    assert(i > 10) else $info("Not greater than 10: %0d", i);
    assert(i > 9) else $fatal(2);
endfunction

localparam p = foo(8);
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InfoTask);
    CHECK(diags[1].code == diag::FatalTask);
}

TEST_CASE("Deferred assertion void-returning system funcs allowed regress GH #925") {
    auto tree = SyntaxTree::fromText(R"(
module Test;
  function logic my_func();
    static logic my_var = 1'b1;
    assert final (my_var == 1'b1)
      else $error();
  endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("System function call args are not considered 'top-level' statements") {
    auto tree = SyntaxTree::fromText(R"(
module my_mod;
  function automatic logic my_func();
    my_func = 1'b1;
    assert (my_func === 1'b1)
      else $error("Expect my_func to return 1 but got %0b", my_func);
  endfunction
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowRecursiveImplicitCall;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("$bits of >32bit sized type") {
    auto tree = SyntaxTree::fromText(R"(
logic [7:0] a [2147483647];
localparam p = $bits(a);
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& p = compilation.getCompilationUnits()[0]->find<ParameterSymbol>("p");
    CHECK(p.getValue().integer() == -8);
}

TEST_CASE("Restriction on automatic variables in $past") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        automatic int b;
        automatic int c = $past(b, 1, b > 0, @b);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::AutoFromNonProcedural);
    CHECK(diags[1].code == diag::AutoFromNonProcedural);
}

TEST_CASE("$isunbounded of non-param name") {
    auto tree = SyntaxTree::fromText(R"(
localparam p = $isunbounded(1 + 1);
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::IsUnboundedParamArg);
}

TEST_CASE("$stacktrace function") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        string s;
        $stacktrace;
        s = $stacktrace;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Annex D option system tasks and functions") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire n = 1;
    initial begin : baz
        bit f;
        int a, b, c, d, e;
        f = $countdrivers(m.n, a, b, c, d, e);
        $list;
        $list(m);
        $input("asdf");
        $key("asdf");
        $nokey;
        $reset;
        $reset(0, 1, 2);
        a = $reset_count;
        b = $reset_value;
        $save("SDF");
        $reset("SDF");
        $incsave("SDF");
        $scope(m.baz);
        c = $scale(m);
        $showscopes;
        $showscopes(1);
        $showvars;
        $showvars(a, b[0]);
    end

    logic [1:4] in_mem[100];
    assign {i1,i2,i3,i4} = $getpattern(in_mem[n]);

    initial begin
        $sreadmemb(in_mem, 0, 1, "SDF");
        $sreadmemh(in_mem, 0, 1, "SDF", "BAZ");
    end

    var v;
    initial begin
        bit b;
        b = $countdrivers(v);
        $list(m.n);
        $showvars(v + 1);
        $sreadmemh(in_mem, 0, 1, "SDF", in_mem);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ExpectedNetRef);
    CHECK(diags[1].code == diag::ExpectedScopeName);
    CHECK(diags[2].code == diag::ExpectedVariableName);
    CHECK(diags[3].code == diag::BadSystemSubroutineArg);
}

TEST_CASE("$sformat invalid %p call") {
    auto tree = SyntaxTree::fromText(R"(
function void void_fn;
endfunction

module m;
  initial begin
    $sformatf("%p", void_fn());
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::FormatMismatchedType);
}
