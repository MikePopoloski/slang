// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/driver/Driver.h"

using namespace slang::driver;

TEST_CASE("Duplicate modules in different source libraries") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);
    auto lib2 = std::make_unique<SourceLibrary>("lib2", 2);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib2.get());
    auto tree3 = SyntaxTree::fromText(R"(
module top;
    mod m();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;

    auto& lib =
        compilation.getRoot().lookupName<InstanceSymbol>("top.m").getDefinition().sourceLibrary;
    CHECK(&lib == lib1.get());
}

TEST_CASE("Driver library default ordering") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo --libmap \"{0}libtest/testlib.map\" \"{0}libtest/top.sv\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));

    auto& m = compilation->getRoot().lookupName<InstanceSymbol>("top.m");
    CHECK(m.getDefinition().sourceLibrary.name == "lib1");
}

TEST_CASE("Driver library explicit ordering") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format(
        "testfoo --libmap \"{0}libtest/testlib.map\" \"{0}libtest/top.sv\" -Llib2,lib1", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    CHECK(driver.reportCompilation(*compilation, false));

    auto& m = compilation->getRoot().lookupName<InstanceSymbol>("top.m");
    CHECK(m.getDefinition().sourceLibrary.name == "lib2");
}

TEST_CASE("Top module in a library") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
module top;
endmodule
)");

    CompilationOptions options;
    options.topModules.emplace("lib1.mod");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto topInstances = compilation.getRoot().topInstances;
    CHECK(topInstances.size() == 1);
    CHECK(topInstances[0]->name == "mod");
}

TEST_CASE("Config block top modules") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    localparam int i = 1;
    design frob;
endconfig

module frob;
endmodule

module bar;
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto topInstances = compilation.getRoot().topInstances;
    CHECK(topInstances.size() == 1);
    CHECK(topInstances[0]->name == "frob");
}

TEST_CASE("Config in library, disambiguate with module name") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);
    auto lib2 = std::make_unique<SourceLibrary>("lib2", 2);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule

config cfg;
    design mod;
endconfig
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
module mod;
endmodule

module cfg;
endmodule

config cfg;
    design mod;
endconfig
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib2.get());
    auto tree3 = SyntaxTree::fromText(R"(
module mod;
endmodule

config cfg;
    design mod;
endconfig
)");

    CompilationOptions options;
    options.topModules.emplace("lib2.cfg:config");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;

    auto top = compilation.getRoot().topInstances[0];
    CHECK(top->name == "mod");
    CHECK(top->getDefinition().sourceLibrary.name == "lib2");
}

TEST_CASE("Config that targets library cell") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
config cfg;
    design lib1.mod;
endconfig
)");

    CompilationOptions options;
    options.topModules.emplace("cfg");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Config block error missing module") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design frob libfoo.bar;
endconfig
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InvalidTopModule);
    CHECK(diags[1].code == diag::InvalidTopModule);
}

TEST_CASE("Config default liblist") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
module mod;
endmodule

module top;
    mod m1();
endmodule

config cfg;
    design top;
    default liblist lib1;
endconfig
)");

    CompilationOptions options;
    options.topModules.emplace("cfg");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto& m1 = compilation.getRoot().lookupName<InstanceSymbol>("top.m1");
    auto& lib = m1.getDefinition().sourceLibrary;
    CHECK(lib.name == "lib1");
}

TEST_CASE("Config cell overrides") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());
    auto tree2 = SyntaxTree::fromText(R"(
module mmm;
endmodule

module nnn;
endmodule

module top;
    mod m1();
    foo f1();
    bar b1();
    nnn n1();
endmodule

config cfg;
    design top;
    cell mod liblist lib1;
    cell foo use mmm;
    cell bar use lib1.mod;
endconfig
)");

    CompilationOptions options;
    options.topModules.emplace("cfg");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Config instance overrides") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b.f2 use bar;
endconfig

module foo;
endmodule

module bar;
endmodule

module baz;
    foo f1(), f2();
endmodule

module top;
    baz b();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& inst = compilation.getRoot().lookupName<InstanceSymbol>("top.b.f2");
    CHECK(inst.getDefinition().name == "bar");
}

TEST_CASE("Config instance override errors") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b.f2 use bar;
    instance top.b.f3 use somelib.foo;
    instance top.b.f4 use lib1.mod;
    instance top.b.f5 use lib1.foo;
    instance top.b.f6 liblist lib1;
    instance top.i.p use foo;
endconfig

module foo;
endmodule

module baz;
    foo f1(), f2();
    foo f3(), f4(), f5(), f6();
endmodule

module top;
    baz b();
    I i();
endmodule

program prog;
endprogram

interface I;
    prog p(), q();
endinterface
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::UnknownModule);
    CHECK(diags[1].code == diag::UnknownLibrary);
    CHECK(diags[2].code == diag::UnknownModule);
    CHECK(diags[3].code == diag::UnknownModule);
    CHECK(diags[4].code == diag::InvalidInstanceForParent);
}

TEST_CASE("Config inherited liblist") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);
    auto lib2 = std::make_unique<SourceLibrary>("lib2", 2);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
module baz;
    mod m();
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib2.get());

    auto tree3 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b liblist lib1 lib2;
endconfig

module top;
    baz b();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree3);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Config hierarchical config target") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module qq;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b use cfg2;
endconfig

config cfg2;
    design baz;
    instance baz.f1 use mod;
    instance baz.f1 liblist lib1;
endconfig

module mod;
    qq q1();
endmodule

module baz;
    foo f1();
endmodule

module top;
    baz b();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Config instance paths with two roots") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design foo bar;
    instance foo.a use m1;
    instance bar.a use m2;
endconfig

module m1;
endmodule

module m2;
endmodule

module foo;
    some_mod a();
endmodule

module bar;
    some_mod a();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto& fooA = root.lookupName<InstanceSymbol>("foo.a");
    CHECK(fooA.getDefinition().name == "m1");

    auto& barA = root.lookupName<InstanceSymbol>("bar.a");
    CHECK(barA.getDefinition().name == "m2");
}

TEST_CASE("Config warning / error cases") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top top;
    default liblist foo;
    cell b use c;
    cell b use d;
    instance top.foo use lib1.c;
    instance top.foo use d;
    instance foo.bar use e;
    instance top.blah1 use qq;
    instance top.blah2 use rr;
    instance top.blah2 use #(.A(1));
    cell foo.bar use baz;
endconfig

module a; endmodule
module b; endmodule

config qq;
    design a b;
endconfig

config rr;
    design a;
endconfig

module top;
    asdf blah1();
    asdf blah2();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 10);
    CHECK(diags[0].code == diag::ConfigDupTop);
    CHECK(diags[1].code == diag::WarnUnknownLibrary);
    CHECK(diags[2].code == diag::UnusedConfigCell);
    CHECK(diags[3].code == diag::DupConfigRule);
    CHECK(diags[4].code == diag::UnusedConfigInstance);
    CHECK(diags[5].code == diag::DupConfigRule);
    CHECK(diags[6].code == diag::ConfigInstanceWrongTop);
    CHECK(diags[7].code == diag::ConfigParamsIgnored);
    CHECK(diags[8].code == diag::WarnUnknownLibrary);
    CHECK(diags[9].code == diag::NestedConfigMultipleTops);
}

TEST_CASE("Config rules with param overrides") {
    auto tree = SyntaxTree::fromText(R"(
module adder #(parameter ID = "id", W = 8, D = 512)();
    initial $display("ID = %s, W = %d, D = %d", ID, W, D);
endmodule : adder

module top;
    parameter WIDTH = 16;
    adder a1();
endmodule

config cfg1;
    design work.top;
    instance top use #(.WIDTH(32));
    instance top.a1 use #(.W(top.WIDTH));
endconfig

module top4 ();
    parameter S = 16;
    adder #(.ID("a1")) a1();
    adder #(.ID("a2")) a2();
    adder #(.ID("a3")) a3();
    adder #(.ID("a4")) a4();
endmodule

config cfg2;
    localparam S = 24;
    design top4;
    instance top4.a1 use #(.W(top4.S));
    instance top4.a2 use #(.W(S));
endconfig

module top5 ();
    parameter WIDTH = 64, DEPTH = 1024, ID = "A1";
    adder #(.ID(ID), .W(WIDTH), .D(DEPTH)) a1();
endmodule

config cfg3;
    design top5;
    instance top5.a1 use #(.W());
endconfig

module top6 ();
    adder #(.W(64), .D(1024)) a1();
endmodule

config cfg4;
    design top6;
    instance top6.a1 use #();
endconfig

module test;
    top8 t();
    defparam t.WIDTH = 64;
    defparam t.a1.W = 16;
endmodule

module top8 ();
    parameter WIDTH = 32;
    adder #(.ID("a1")) a1();
    adder #(.ID("a2"), .W(WIDTH)) a2();
endmodule

config cfg6;
    design test;
    instance test.t use #(.WIDTH(48));
endconfig
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");
    options.topModules.emplace("cfg2");
    options.topModules.emplace("cfg3");
    options.topModules.emplace("cfg4");
    options.topModules.emplace("cfg6");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto getParam = [&](std::string_view name) {
        auto& param = compilation.getRoot().lookupName<ParameterSymbol>(name);
        return param.getValue();
    };

    CHECK(getParam("top.a1.W").integer() == 32);
    CHECK(getParam("top.a1.D").integer() == 512);
    CHECK(getParam("top4.a1.W").integer() == 16);
    CHECK(getParam("top4.a2.W").integer() == 24);
    CHECK(getParam("top5.a1.W").integer() == 8);
    CHECK(getParam("top5.a1.D").integer() == 1024);
    CHECK(getParam("top6.a1.W").integer() == 8);
    CHECK(getParam("top6.a1.D").integer() == 512);
    CHECK(getParam("test.t.a1.W").integer() == 16);
    CHECK(getParam("test.t.a2.W").integer() == 48);
}

TEST_CASE("Config cell overrides with param assignments") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    cell top use #(.A(1));
    cell f use #(.B(2));
endconfig

module f #(parameter int B);
endmodule

module top #(parameter int A);
    f foo();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto getParam = [&](std::string_view name) {
        auto& param = compilation.getRoot().lookupName<ParameterSymbol>(name);
        return param.getValue();
    };

    CHECK(getParam("top.A").integer() == 1);
    CHECK(getParam("top.foo.B").integer() == 2);
}

TEST_CASE("Config param overrides with nested config path") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    cell f use cfg2 : config;
endconfig

config cfg2;
    design f;
    cell f use #(.B(5));
endconfig

module f #(parameter int B);
endmodule

module top;
    f foo();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto getParam = [&](std::string_view name) {
        auto& param = compilation.getRoot().lookupName<ParameterSymbol>(name);
        return param.getValue();
    };

    CHECK(getParam("top.foo.B").integer() == 5);
}

TEST_CASE("Config cell overrides with specific target lib") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module qq;
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    cell lib1.f use #(.A(4));
    cell lib1.f use baz;
    cell top liblist lib1;
endconfig

module baz #(parameter int A);
endmodule

module top;
    f foo();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree1);
    NO_COMPILATION_ERRORS;

    auto getParam = [&](std::string_view name) {
        auto& param = compilation.getRoot().lookupName<ParameterSymbol>(name);
        return param.getValue();
    };

    CHECK(getParam("top.foo.A").integer() == 4);
}

TEST_CASE("Config override top cell with specific target lib") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module qq #(parameter int A);
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
config cfg1;
    design lib1.qq;
    cell lib1.qq use #(.A(4));
    cell qq use #(.A(5));
endconfig
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree2);
    compilation.addSyntaxTree(tree1);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedConfigCell);

    auto getParam = [&](std::string_view name) {
        auto& param = compilation.getRoot().lookupName<ParameterSymbol>(name);
        return param.getValue();
    };

    CHECK(getParam("qq.A").integer() == 4);
}

TEST_CASE("Config invalid top cell override rule") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top use foo;
endconfig

config cfg2;
    design top2;
    cell top2 use foo;
endconfig

module top;
endmodule

module top2;
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");
    options.topModules.emplace("cfg2");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConfigOverrideTop);
    CHECK(diags[1].code == diag::ConfigOverrideTop);
}

TEST_CASE("Duplicate config blocks") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top use foo;
endconfig

config cfg1;
    design top;
endconfig
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::Redefinition);
}

TEST_CASE("Config instance path underneath a hierarchical config error") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    cell f use cfg2 : config;
    instance top.foo.q use l;
endconfig

config cfg2;
    design bar;
endconfig

module bar;
endmodule

module top;
    f foo();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConfigInstanceUnderOtherConfig);
}

TEST_CASE("Multiple tops with same name error") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
endconfig

config cfg2;
    design top;
endconfig

module top;
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");
    options.topModules.emplace("cfg2");
    options.topModules.emplace("top");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MultipleTopDupName);
    CHECK(diags[1].code == diag::MultipleTopDupName);
}

TEST_CASE("Displaying library binding info") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);

    auto tree1 = SyntaxTree::fromText(R"(
module foo;
    localparam string S = $sformatf("%L");
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.foo use lib1.foo;
endconfig

module top;
    f foo();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto& param = compilation.getRoot().lookupName<ParameterSymbol>("top.foo.S");
    CHECK(param.getValue().str() == "lib1.foo");
}

TEST_CASE("Config params target primitives") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.foo use p1;
    cell bar use p2;
    cell bar use #(.A(1));
    instance top.foo use #(.B(1));
endconfig

primitive p1 (output c, input a, b);
    table 00:0; endtable
endprimitive

primitive p2 (output c, input a, b);
    table 00:0; endtable
endprimitive

module top;
    f foo(c, a, b);
    bar bar(c, a, b);
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConfigParamsForPrimitive);
    CHECK(diags[1].code == diag::ConfigParamsForPrimitive);
}

TEST_CASE("Config target multiple primitives") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b1 use p1;
    instance top.b2 use p1;
endconfig

primitive p1 (output c, input a, b);
    table 00:0; endtable
endprimitive

module top;
    bar b1(c, a, b), b2(c, a, b);
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Config prim instance with module override") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    cell foo use m;
    instance top.b2 use m;
endconfig

module m #(parameter int A);
endmodule

module top;
    foo (supply0, pull1) b1();
    baz #3 b2(), b3();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");
    options.flags |= CompilationFlags::AllowBareValParamAssignment;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::InstanceWithStrength);
    CHECK(diags[1].code == diag::UnknownPrimitive);
}

TEST_CASE("Config target multiple primitives with explicit primitive syntax") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.b1 use p1;
    instance top.b2 use p1;
endconfig

primitive p1 (output c, input a, b);
    table 00:0; endtable
endprimitive

module top;
    bar (supply0, pull1) b1(c, a, b), b2(c, a, b);
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Configs with binds") {
    auto lib1 = std::make_unique<SourceLibrary>("lib1", 1);
    auto lib2 = std::make_unique<SourceLibrary>("lib2", 2);

    auto tree1 = SyntaxTree::fromText(R"(
module mod;
endmodule

module baz #(parameter int A);
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib1.get());

    auto tree2 = SyntaxTree::fromText(R"(
module foo;
    m m2();
endmodule
)",
                                      SyntaxTree::getDefaultSourceManager(), "source", "", {},
                                      lib2.get());

    auto tree3 = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.m1 liblist lib1;
    cell next liblist work lib2;
    cell baz liblist lib1;
    cell baz use #(.A(1));
endconfig

module m;
    localparam int J = 9;
endmodule

module next;
    bind top.m1 foo f1();
    bind top.m1 baz baz1();
endmodule

module top;
    mod m1();
    next n1();
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree1);
    compilation.addSyntaxTree(tree3);
    compilation.addSyntaxTree(tree2);
    NO_COMPILATION_ERRORS;

    auto& param = compilation.getRoot().lookupName<ParameterSymbol>("top.m1.f1.m2.J");
    CHECK(param.getValue().integer() == 9);
}

TEST_CASE("Configs with libraries and interconnect busses example") {
    auto realLib = std::make_unique<SourceLibrary>("realLib", 1);
    auto logicLib = std::make_unique<SourceLibrary>("logicLib", 2);

    auto cfgs = SyntaxTree::fromText(R"(
config cfgReal;
    design logicLib.top;
    default liblist realLib logicLib;
endconfig

config cfgLogic;
    design logicLib.top;
    default liblist logicLib realLib;
endconfig
)");

    auto topSv = SyntaxTree::fromText(R"(
module top();
    interconnect aBus[0:3][0:1];
    logic [0:3] dBus;
    driver driverArray[0:3](aBus);
    cmp cmpArray[0:3](aBus,rst,dBus);
endmodule : top
)",
                                      SyntaxTree::getDefaultSourceManager(), "top.sv", "", {},
                                      logicLib.get());

    auto netsPkg = SyntaxTree::fromText(R"(
package NetsPkg;
    nettype real realNet;
endpackage : NetsPkg
)");

    auto driverSvr = SyntaxTree::fromText(R"(
module driver
    import NetsPkg::*;
    #(parameter int delay = 30,
                int iterations = 256)
    (output realNet out[0:1]);
    timeunit 1ns / 1ps;
    real outR[1:0];
    assign out = outR;
    initial begin
        outR[0] = 0.0;
        outR[1] = 3.3;
        for (int i = 0; i < iterations; i++) begin
            #delay outR[0] += 0.2;
            outR[1] -= 0.2;
        end
    end
endmodule : driver
)",
                                          SyntaxTree::getDefaultSourceManager(), "driver.svr", "",
                                          {}, realLib.get());

    auto driverSv = SyntaxTree::fromText(R"(
module driver #(parameter int delay = 30,
                          int iterations = 256)
               (output wire logic out[0:1]);
    timeunit 1ns / 1ps;
    logic [0:1] outvar;

    assign out[0] = outvar[0];
    assign out[1] = outvar[1];

    initial begin
        outvar = '0;
        for (int i = 0; i < iterations; i++)
            #delay outvar++;
    end
endmodule : driver
)",
                                         SyntaxTree::getDefaultSourceManager(), "driver.sv", "", {},
                                         logicLib.get());

    auto cmpSvr = SyntaxTree::fromText(R"(
module cmp
    import NetsPkg::*;
    #(parameter real hyst = 0.65)
    (input realNet inA[0:1],
     input logic rst,
     output logic out);
    timeunit 1ns / 1ps;
    real updatePeriod = 100.0;

    initial out = 1'b0;

    always #updatePeriod begin
        if (rst) out <= 1'b0;
        else if (inA[0] > inA[1]) out <= 1'b1;
        else if (inA[0] < inA[1] - hyst) out <= 1'b0;
    end
endmodule : cmp
)",
                                       SyntaxTree::getDefaultSourceManager(), "cmp.svr", "", {},
                                       realLib.get());

    auto cmpSv = SyntaxTree::fromText(R"(
module cmp #(parameter real hyst = 0.65)
            (input wire logic inA[0:1],
             input logic rst,
             output logic out);

    initial out = 1'b0;

    always @(inA[0], inA[1], rst) begin
        if (rst) out <= 1'b0;
        else if (inA[0] & ~inA[1]) out <= 1'b1;
        else out <= 1'b0;
    end
endmodule : cmp
)",
                                      SyntaxTree::getDefaultSourceManager(), "cmp.sv", "", {},
                                      logicLib.get());

    for (auto cfgName : {"cfgReal", "cfgLogic"}) {
        CompilationOptions options;
        options.topModules.emplace(cfgName);
        options.defaultTimeScale = TimeScale::fromString("1ns/1ns");

        Compilation compilation(options);
        compilation.addSyntaxTree(cfgs);
        compilation.addSyntaxTree(topSv);
        compilation.addSyntaxTree(netsPkg);
        compilation.addSyntaxTree(driverSvr);
        compilation.addSyntaxTree(driverSv);
        compilation.addSyntaxTree(cmpSvr);
        compilation.addSyntaxTree(cmpSv);
        NO_COMPILATION_ERRORS;
    }
}

TEST_CASE("Configs with virtual interfaces") {
    auto tree = SyntaxTree::fromText(R"(
config cfg1;
    design top;
    instance top.i use J;
    cell I use J;
endconfig

interface J;
endinterface

module top;
    I i();
    virtual I vi = i;
endmodule
)");
    CompilationOptions options;
    options.topModules.emplace("cfg1");

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::VirtualIfaceConfigRule);
}
