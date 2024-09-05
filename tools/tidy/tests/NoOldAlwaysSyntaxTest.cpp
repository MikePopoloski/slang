// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("NoOldAlwaysSyntax: Use of old always_comb syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;

    always @(*) begin
        c = a + b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoOldAlwaysSyntax: Use of old always_ff syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;

    always @(posedge a) begin
        c <= a + b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoOldAlwaysSyntax: Use of SV always_ff and always_comb syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    logic a, b, c;
    logic d, e, f;

    always_ff @(posedge a) begin
        c <= a + b;
    end

    always_comb begin
        d = e + f;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoOldAlwaysSyntax: Assertion") {
    auto tree = SyntaxTree::fromText(R"(
module top(input logic clk, input logic rst);
    logic a, b;

    test : assert property (
        @(posedge clk) disable iff (rst) a |-> b) else $error("error");
    )
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoOldAlwaysSyntax: Sequence") {
    auto tree = SyntaxTree::fromText(R"(
module top(input logic clk);
    logic a, b;

    sequence;
        @(posedge clk) a |-> b
    endsequence
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoOldAlwaysSyntax: Covergroup") {
    auto tree = SyntaxTree::fromText(R"(
module top(input logic clk, input logic rst);
    logic a;

    covergroup cg @(posedge clk);
        coverpoint a;
    endgroup
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoOldAlwaysSyntax: Legit use of old always") {
    auto tree = SyntaxTree::fromText(R"(
module top(input logic clk, input logic rst);
    logic busy, start, n, pause;

    always @(posedge clk) begin
        automatic int f;
        if (busy) begin
            assume (!start);
            assume ($stable(n));
        end

        if (done) begin
            case ($past(n))
                0: assert (f == 1);
                1: assert (f == 1);
                2: assert (f == 2);
                3: assert (f == 3);
                4: assert (f == 5);
                5: assert (f == 8);
            endcase
            cover (f == 13);
            cover (f == 144);
            cover ($past(n) == 15);
        end

        assume property (s_eventually !pause);

        if (start && !pause)
            assert property (s_eventually done);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoOldAlwaysSyntax: composite lhs") {
    auto tree = SyntaxTree::fromText(R"(
module top();
    logic n;

    always @(*) begin
        {n} = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoOldAlwaysSyntax");
    bool result = visitor->check(root);
    CHECK(result);
}
