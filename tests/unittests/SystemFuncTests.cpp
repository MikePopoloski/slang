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
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 22);
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

    initial begin
        $readmemb("F");
        $readmemb(3.4, "asdf");
        $readmemb(3.4, foo);
        $readmemb("asdf", foo);
        $readmemb("asdf", bar);
        $readmemb("asdf", baz, s);
        $readmemb("asdf", baz, 1, s);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::TooFewArguments);
    CHECK(diags[1].code == diag::ExpressionNotAssignable);
    CHECK(diags[2].code == diag::BadSystemSubroutineArg);
    CHECK(diags[3].code == diag::BadSystemSubroutineArg);
    CHECK(diags[4].code == diag::BadSystemSubroutineArg);
    CHECK(diags[5].code == diag::BadSystemSubroutineArg);
    CHECK(diags[6].code == diag::BadSystemSubroutineArg);
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

    // [20.3] Simulation time functions
    CHECK(typeof("$time") == "time");
    CHECK(typeof("$stime") == "bit[31:0]");
    CHECK(typeof("$realtime") == "realtime");

    // [20.15] Probabilistic distribution functions
    CHECK(typeof("$random") == "int");

    // [18.13] Constrained pseudo-random value generation
    CHECK(typeof("$urandom") == "bit[31:0]");

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

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
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
}