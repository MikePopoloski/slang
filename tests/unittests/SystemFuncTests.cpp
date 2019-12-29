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
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 18);
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