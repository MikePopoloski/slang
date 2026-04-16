// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>
#include <fstream>
#include <regex>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/driver/Driver.h"
#include "slang/text/SourceManager.h"

using namespace slang::driver;

static bool stdoutContains(std::string_view text) {
    return OS::capturedStdout.find(text) != std::string::npos;
}

static bool stderrContains(std::string_view text) {
    return OS::capturedStderr.find(text) != std::string::npos;
}

TEST_CASE("Driver basic") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
}

TEST_CASE("Driver valid column unit") {
    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";

    const char* argv1[] = {"testfoo", "--diag-column-unit=byte", filePath.c_str()};
    CHECK(driver.parseCommandLine(3, argv1));
    CHECK(driver.processOptions());
    CHECK(driver.options.diagColumnUnit == ColumnUnit::Byte);

    const char* argv2[] = {"testfoo", "--diag-column-unit=display", filePath.c_str()};
    CHECK(driver.parseCommandLine(3, argv2));
    CHECK(driver.processOptions());
    CHECK(driver.options.diagColumnUnit == ColumnUnit::Display);
}

TEST_CASE("Driver file preprocess -- obfuscation") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto filePath = findTestDir() + "test.sv";
    const char* argv[] = {"testfoo", filePath.c_str()};
    CHECK(driver.parseCommandLine(2, argv));
    CHECK(driver.processOptions());
    CHECK(driver.runPreprocessor(PreprocessOutputFlags::IncludeComments |
                                 PreprocessOutputFlags::ObfuscateIds |
                                 PreprocessOutputFlags::UseFixedObfuscationSeed));

    auto output = OS::capturedStdout;
    output = std::regex_replace(output, std::regex("\r\n"), "\n");

    CHECK(output.starts_with("\nmodule AOOpUHNpKPjVcKHQ;\n"
                             "    // hello\n"
                             "    int LMxOpJDziyYJoPIV = 32'haa_bb??e;\n"
                             "    string pmOPtNbMAqvklYVm = "));

    CHECK(output.ends_with(";\n"
                           "    begin end\n"
                           "endmodule\n"
                           "\n"));
}

TEST_CASE("Driver command files are processed strictly in order") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}\"test.sv -F \"{0}cmd3.f\"", findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());

    std::vector<std::string_view> fileNames;
    for (auto buffer : driver.sourceLoader.loadSources()) {
        auto name = driver.sourceManager.getRawFileName(buffer.id);
        if (auto idx = name.find_last_of("/\\"); idx != name.npos)
            name = name.substr(idx + 1);

        fileNames.push_back(name);
    }

    CHECK(fileNames.size() == 4);
    CHECK(std::ranges::is_sorted(fileNames));
}

static bool contains(std::string_view str, std::string_view value) {
    return str.find(value) != std::string_view::npos;
}

TEST_CASE("Driver library files with explicit name") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --single-unit --libraries-inherit-macros "
                            " \"-I{0}/nested\" \"-vlibfoo={0}/library/.../*.sv\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        // Ignore include files and macro buffers.
        if (sm.isMacroLoc(SourceLocation(buf, 0)) || sm.getIncludedFrom(buf))
            continue;

        auto lib = sm.getLibraryFor(buf);
        auto name = sm.getRawFileName(buf);
        if (contains(name, "test6.sv")) {
            CHECK(!lib);
        }
        else {
            REQUIRE(lib);
            CHECK(lib->name == "libfoo");
        }
    }
}

TEST_CASE("Driver load library maps") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\"", testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        // Ignore include files and macro buffers.
        if (sm.isMacroLoc(SourceLocation(buf, 0)) || sm.getIncludedFrom(buf))
            continue;

        auto name = sm.getRawFileName(buf);
        if (contains(name, ".map"))
            continue;

        auto lib = sm.getLibraryFor(buf);
        REQUIRE(lib);
        if (contains(name, "libmod.qv") || contains(name, "pkg.sv") || contains(name, "other.sv")) {
            CHECK(lib->name == "libfoo");
        }
        else {
            CHECK(lib->name == "libsys");
        }
    }

    CHECK(driver.sourceLoader.getLibraryMaps().size() == 2);
}

TEST_CASE("Driver file kind tracking") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo \"{0}test6.sv\" --libmap \"{0}/library/lib.map\" -v "
                            "\"{0}test5.sv\" \"{0}test6.sv\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto& sm = driver.sourceManager;
    for (auto buf : sm.getAllBuffers()) {
        auto name = sm.getRawFileName(buf);
        auto kind = sm.getBufferKind(buf);
        if (contains(name, ".map"))
            CHECK(kind == SourceManager::BufferKind::LibraryMap);
        else if (contains(name, "test5.sv"))
            CHECK(kind == SourceManager::BufferKind::LibraryFile);
        else if (contains(name, "test6.sv"))
            CHECK(kind == SourceManager::BufferKind::DesignFile);
        else if (contains(name, "macro.svh"))
            CHECK(kind == SourceManager::BufferKind::IncludeFile);
    }
}

TEST_CASE("Driver separate unit listing") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test5.sv\" -C \"{0}unit.f\" -v \"lib2={0}test6.sv\"",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, false);
    CHECK(driver.reportDiagnostics(false));
    CHECK(stdoutContains("Build succeeded"));

    auto& root = compilation->getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->getSourceLibrary()->name == "work");
    CHECK(root.topInstances[0]->name == "k");

    auto units = compilation->getCompilationUnits();
    REQUIRE(units.size() == 3);
    REQUIRE(units[1]->getSourceLibrary() != nullptr);
    REQUIRE(units[2]->getSourceLibrary() != nullptr);
    CHECK(units[1]->getSourceLibrary()->name == "lib2");
    CHECK(units[2]->getSourceLibrary()->name == "mylib");

    auto defs = compilation->getDefinitions();
    auto it = std::ranges::find_if(defs, [](auto sym) {
        return sym->kind == SymbolKind::Definition && sym->name == "mod1" &&
               sym->getSourceLibrary() && sym->getSourceLibrary()->name == "mylib";
    });
    CHECK(it != defs.end());
}

TEST_CASE("Driver customize default lib name") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto args = fmt::format("testfoo \"{0}test5.sv\" -v \"blah={0}test6.sv\" --defaultLibName blah",
                            findTestDir());
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());

    auto compilation = driver.createCompilation();
    driver.reportCompilation(*compilation, false);
    CHECK(driver.reportDiagnostics(false));
    CHECK(stdoutContains("Build succeeded"));

    auto& root = compilation->getRoot();
    REQUIRE(root.topInstances.size() == 1);
    CHECK(root.topInstances[0]->getSourceLibrary()->name == "blah");
    CHECK(root.topInstances[0]->name == "k");

    auto units = compilation->getCompilationUnits();
    REQUIRE(units.size() == 2);
    REQUIRE(units[0]->getSourceLibrary() != nullptr);
    REQUIRE(units[1]->getSourceLibrary() != nullptr);
    CHECK(units[0]->getSourceLibrary()->name == "blah");
    CHECK(units[1]->getSourceLibrary()->name == "blah");
}

TEST_CASE("Driver single-unit gives library files their own tree") {
    auto guard = OS::captureOutput();

    Driver driver;
    driver.addStandardArgs();

    auto testDir = findTestDir();
    auto args = fmt::format("testfoo --single-unit "
                            "\"{0}libsplit_top.sv\" \"{0}libsplit_lib.sv\" "
                            "--libmap \"{0}libsplit.map\"",
                            testDir);
    CHECK(driver.parseCommandLine(args));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.reportParseDiags());

    REQUIRE(driver.syntaxTrees.size() == 2);

    int defaultUnits = 0, libraryUnits = 0;
    for (auto& tree : driver.syntaxTrees) {
        if (tree->isLibraryUnit)
            ++libraryUnits;
        else
            ++defaultUnits;
    }
    CHECK(defaultUnits == 1);
    CHECK(libraryUnits == 1);
}

TEST_CASE("Driver ClockVarTargetAssign -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM prohibits continuous assignments to output clockvars.
    // In strict (default) mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module m(input clk);
    int j;
    assign j = 1;
    clocking cb @(posedge clk);
        output j;
    endclocking
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("clockvar-target-assign"));
}

TEST_CASE("Driver ClockVarTargetAssign -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools accept continuous assignments to output clockvars; in --compat=all
    // slang should downgrade the diagnostic from error to warning.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module m(input clk);
    int j;
    assign j = 1;
    clocking cb @(posedge clk);
        output j;
    endclocking
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("clockvar-target-assign"));
}

TEST_CASE("Driver CrossIdentInBinsof -- error in strict mode") {
    auto guard = OS::captureOutput();

    // According to the LRM cross_identifier is not a valid bins_expression.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module m;
    logic clk, a, b, c;
    covergroup cg @(posedge clk);
        cp_a : coverpoint a { bins zero = {0}; bins one = {1}; }
        cp_b : coverpoint b { bins zero = {0}; bins one = {1}; }
        cp_c : coverpoint c { bins zero = {0}; bins one = {1}; }
        cp_a_cross_b : cross cp_a, cp_b {
            bins both_one = binsof(cp_a.one) && binsof(cp_b.one);
        }
        cp_nested : cross cp_a_cross_b, cp_c {
            bins with_c = binsof(cp_a_cross_b) && binsof(cp_c.one);
        }
    endgroup
    cg cg_inst = new();
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("cross-ident-in-binsof"));
}

TEST_CASE("Driver CrossIdentInBinsof -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools accept cross identifiers in binsof(); --compat=all downgrades to warning.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module m;
    logic clk, a, b, c;
    covergroup cg @(posedge clk);
        cp_a : coverpoint a { bins zero = {0}; bins one = {1}; }
        cp_b : coverpoint b { bins zero = {0}; bins one = {1}; }
        cp_c : coverpoint c { bins zero = {0}; bins one = {1}; }
        cp_a_cross_b : cross cp_a, cp_b {
            bins both_one = binsof(cp_a.one) && binsof(cp_b.one);
        }
        cp_nested : cross cp_a_cross_b, cp_c {
            bins with_c = binsof(cp_a_cross_b) && binsof(cp_c.one);
        }
    endgroup
    cg cg_inst = new();
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("cross-ident-in-binsof"));
}

TEST_CASE("Driver NonstandardConstraintBlock -- error in strict mode") {
    auto guard = OS::captureOutput();

    // According to the LRM braced constraint_set is not valid as a top-level constraint item.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
`define CREATE_VSEQ(SEQ_NAME, CONSTRAINTS) \
  class SEQ_NAME; \
    rand int x; \
    constraint c { CONSTRAINTS } \
  endclass : SEQ_NAME

`CREATE_VSEQ(my_vseq, {
    x inside {0, 1};
})
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("nonstandard-constraint-block"));
}

TEST_CASE("Driver NonstandardConstraintBlock -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools accept nested constraint blocks with a warning; --compat=all keeps the
    // diagnostic as a warning (build succeeds, diagnostic still visible).
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
`define CREATE_VSEQ(SEQ_NAME, CONSTRAINTS) \
  class SEQ_NAME; \
    rand int x; \
    constraint c { CONSTRAINTS } \
  endclass : SEQ_NAME

`CREATE_VSEQ(my_vseq, {
    x inside {0, 1};
})
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("nonstandard-constraint-block"));
}

TEST_CASE("Driver generic class uninstantiated body -- no diagnostic for same-class assignments") {
    auto guard = OS::captureOutput();

    // In an uninstantiated generic class body T is a formal type parameter; Callback#(T)
    // and Callback#(Base) appear as different types but may be identical once the class is
    // instantiated with T=Base. Slang should compile cleanly with no errors or warnings.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Base; endclass
class Callback #(type T = Base);
  T obj;
endclass
class Handler #(type T = Base);
  function void store(Callback #(T) cb);
    Callback #(Base) b;
    b = cb;
  endfunction
  function bit compare_callback(Callback #(T) cb);
    Callback #(Base) b;
    return (b == cb);
  endfunction
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded: 0 errors"));
}

TEST_CASE("Driver generic class concrete specialization with different types is an error") {
    auto guard = OS::captureOutput();

    // When both class handles are concrete specializations (T fully resolved to a type
    // different from Base), the assignment is genuinely incompatible and must remain an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Base; endclass
class Derived extends Base; endclass
class Callback #(type T = Base);
  T obj;
endclass
module m;
  Callback #(Derived) cd;
  Callback #(Base) cb;
  initial cb = cd;
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
}

TEST_CASE("Driver PortArgRedeclared -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM does not allow a local variable to redeclare a port argument.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Cfg;
  task cntx_alloc(int req_cbb, output int selected_cntx);
    int selected_cntx;
    selected_cntx = req_cbb + 1;
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("port-arg-redeclared"));
}

TEST_CASE("Driver PortArgRedeclared -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools issue a warning (not an error) for local variables redeclaring a port argument;
    // --compat=all keeps the diagnostic as a warning rather than promoting it to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Cfg;
  task cntx_alloc(int req_cbb, output int selected_cntx);
    int selected_cntx;
    selected_cntx = req_cbb + 1;
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("port-arg-redeclared"));
}

TEST_CASE("Driver RefArgForkJoin -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM prohibits referencing a 'ref' argument inside fork-join_any/none.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class TimerTask;
  task run_timer(ref bit restart);
    fork
      begin
        wait(restart == 1);
      end
    join_any
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("ref-arg-in-fork-join"));
}

TEST_CASE("Driver RefArgForkJoin -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools issue a warning (not an error) for ref arguments inside fork-join_any/none;
    // --compat=all keeps the diagnostic as a warning rather than promoting it to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class TimerTask;
  task run_timer(ref bit restart);
    fork
      begin
        wait(restart == 1);
      end
    join_any
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("ref-arg-in-fork-join"));
}

TEST_CASE("Driver CannotIndexScalar -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM does not define a bit-select on a scalar type.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module scalar_bit_indexed;
  bit flag;
  int i;
  initial begin
    i = 0;
    if (flag[i]) $display("set");
  end
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("cannot-index-scalar"));
}

TEST_CASE("Driver CannotIndexScalar -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools issue a warning (not an error) for bit-select on a scalar;
    // --compat=all keeps the diagnostic as a warning rather than promoting it to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module scalar_bit_indexed;
  bit flag;
  int i;
  initial begin
    i = 0;
    if (flag[i]) $display("set");
  end
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("cannot-index-scalar"));
}

TEST_CASE("Driver StringConstraintExpr -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM does not permit string sub-expressions in constraint expressions.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class RegField;
  rand logic [7:0] value;
  string name_str;
  function string get_name(); return name_str; endfunction
  constraint c_by_name {
    if (get_name() == "special") value inside {[1:10]};
  }
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("string-in-constraint"));
}

TEST_CASE("Driver StringConstraintExpr -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools accept string equality in constraint if-conditions with a warning;
    // --compat=all keeps the diagnostic as a warning rather than promoting it to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class RegField;
  rand logic [7:0] value;
  string name_str;
  function string get_name(); return name_str; endfunction
  constraint c_by_name {
    if (get_name() == "special") value inside {[1:10]};
  }
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("string-in-constraint"));
}

TEST_CASE("Driver VirtualArgNameMismatch -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM requires virtual overrides to use identical argument names.
    // In strict mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Base;
  virtual task run(int count);
  endtask
endclass
class Derived extends Base;
  virtual task run(int n);
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("virtual-arg-name-mismatch"));
}

TEST_CASE("Driver VirtualArgNameMismatch -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some tools issue a warning (not an error) for mismatched virtual override argument names;
    // --compat=all keeps the diagnostic as a warning rather than promoting it to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
class Base;
  virtual task run(int count);
  endtask
endclass
class Derived extends Base;
  virtual task run(int n);
  endtask
endclass
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("virtual-arg-name-mismatch"));
}

TEST_CASE("Driver ParameterDoesNotExist -- error in strict mode") {
    auto guard = OS::captureOutput();

    // The LRM does not define behavior when a named parameter override refers
    // to a parameter that does not exist in the instantiated module. In strict
    // mode slang promotes the diagnostic to an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo"};
    CHECK(driver.parseCommandLine(1, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module bot(input clk);
  parameter TYPE = 0;
endmodule

module top;
  logic clk;
  bot #(.TYPE(1), .WIDTH(1)) b(clk);
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(!driver.runFullCompilation());
    CHECK(stdoutContains("Build failed"));
    CHECK(stderrContains("undefined-param-override"));
}

TEST_CASE("Driver ParameterDoesNotExist -- warning in compat mode") {
    auto guard = OS::captureOutput();

    // Some vendor tools issue a warning (not an error) when a named parameter override refers
    // to a non-existent parameter and silently ignores the override;
    // --compat=all keeps the diagnostic as a warning rather than an error.
    Driver driver;
    driver.addStandardArgs();

    const char* argv[] = {"testfoo", "--compat=all"};
    CHECK(driver.parseCommandLine(2, argv));
    driver.sourceLoader.addBuffer(driver.sourceManager.assignText("test.sv", R"(
module bot(input clk);
  parameter TYPE = 0;
endmodule

module top;
  logic clk;
  bot #(.TYPE(1), .WIDTH(1)) b(clk);
endmodule
)"));
    CHECK(driver.processOptions());
    CHECK(driver.parseAllSources());
    CHECK(driver.runFullCompilation());
    CHECK(stdoutContains("Build succeeded"));
    CHECK(stderrContains("undefined-param-override"));
}
