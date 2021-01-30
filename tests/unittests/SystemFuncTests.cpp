#include "Test.h"

TEST_CASE("I/O system tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    string foo;
    int blah[3];

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

    logic [1:0] l;
    
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
        void'($sformatf("%d", s));
        void'($sformatf("%v", l));
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 23);
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
    CHECK(diags[21].code == diag::FormatMismatchedType);
    CHECK(diags[22].code == diag::FormatMismatchedType);
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
        auto tree = SyntaxTree::fromText(string_view(source));
        scope.getCompilation().addSyntaxTree(tree);
        scope.addMembers(tree->root());
    };

    auto typeof = [&](const std::string& source) {
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max);
        return Expression::bind(tree->root().as<ExpressionSyntax>(), context).type->toString();
    };

    // [18.13] Constrained pseudo-random value generation
    CHECK(typeof("$urandom") == "bit[31:0]");
    CHECK(typeof("$urandom_range(1)") == "bit[31:0]");
    CHECK(typeof("$urandom_range(1, 55)") == "bit[31:0]");

    // [20.3] Simulation time functions
    CHECK(typeof("$time") == "time");
    CHECK(typeof("$stime") == "bit[31:0]");
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
        auto tree = SyntaxTree::fromText(string_view(source));
        BindContext context(scope, LookupLocation::max);
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

TEST_CASE("printtimescale -- errors") {
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
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ExpectedModuleName);
    CHECK(diags[1].code == diag::TooManyArguments);
    CHECK(diags[2].code == diag::ExpectedModuleName);
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
        $cast(i, da); // error
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::CastArgSingular);
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
