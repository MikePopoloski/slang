// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/ast/statements/ConditionalStatements.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

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

TEST_CASE("Foreach loop statements") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    bit [3:0][2:1] asdf [5:1][4][1];
endclass

module m;
    C c;
    initial begin
        foreach (c.asdf[i,j,,k]) begin
            if (c.asdf[i][j][0] != 0) begin
                string s;
                s = string'(c.asdf[i][j][0][k]);
                foreach (c.asdf[a]) begin
                    automatic string t = {s, string'(c.asdf[a][i][j][0])};
                    t = {t, "asdf"};
                end
            end
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Foreach loop iterator regression #410") {
    auto tree = SyntaxTree::fromText(R"(
module m #(
    int  N,
    int	 VEC[N]
)();
    always_comb begin
        foreach(VEC[i]) begin
            automatic int v = VEC[i];

            $display(i);
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Foreach loop errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    real foo;
    bit [3:0][2:1] asdf;
    int bar [3][][4];

    initial begin
        foreach (foo[i]) begin end
        foreach (asdf[i,j,]) begin end
        foreach (asdf[i,asdf]) begin end
        foreach (blah[]) begin end
        foreach (bar[, b, c]) begin end
    end

    localparam int asdfasdf[3] = '{1};
    function automatic func;
        foreach (asdfasdf[a]) begin end
    endfunction

    localparam logic f = func();

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::NotAnArray);
    CHECK(diags[1].code == diag::TooManyForeachVars);
    CHECK(diags[2].code == diag::LoopVarShadowsArray);
    CHECK(diags[3].code == diag::UndeclaredIdentifier);
    CHECK(diags[4].code == diag::ForeachDynamicDimAfterSkipped);
    CHECK(diags[5].code == diag::WrongNumberAssignmentPatterns);
}

TEST_CASE("Disable statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin : foo
    end

    task t; endtask

    initial begin : bar
        baz: for (int i = 0; i < 10; i++) begin
            if (i == 4)
                disable m.bar.baz;
            else if (i == 5)
                disable foo;
            else if (i == 6)
                disable bar;
            else if (i == 7)
                disable t;
        end
    end

    int asdf;
    function f; endfunction

    initial begin
        disable asdf;
        disable f;
    end

    function int func;
        disable m.bar.baz;
        return 1;
    endfunction

    localparam int ip = func();

    function int func2;
        automatic int i = 0;
        begin : baz
            for (int j = 0; j < 10; j++) begin : boz
                if (j == 3)
                    disable bar; // illegal in constexpr, target not executing
            end
        end
    endfunction

    localparam int ip2 = func2();

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InvalidDisableTarget);
    CHECK(diags[1].code == diag::InvalidDisableTarget);
    CHECK(diags[2].code == diag::ConstEvalHierarchicalName);
    CHECK(diags[3].code == diag::ConstEvalDisableTarget);
}

TEST_CASE("Delay statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int i;
    logic foo [3];

    initial begin
        #3 i++;
        #(2.1 + real'(i)) i++;

        // Invalid
        #foo i++;
    end

    wire #1step j = 1;

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
    always @((i / 2) or blah, r, (posedge blah or negedge i[0]), edge i[0]);

    always @*;
    always @ *;
    always @(*);
    always @ ( * );

    // warning about constant expr
    localparam int param = 4;
    always @(3);
    always @(posedge 1'(param + 2 / 3));

    // following are invalid
    always @;
    always @(foo or posedge r);
    always @(i iff foo);

    function bar(output o); endfunction
    logic o;
    always @(bar(o));

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::EventExpressionConstant);
    CHECK(diags[1].code == diag::EventExpressionConstant);
    CHECK(diags[2].code == diag::ExpectedIdentifier);
    CHECK(diags[3].code == diag::InvalidEventExpression);
    CHECK(diags[4].code == diag::ExprMustBeIntegral);
    CHECK(diags[5].code == diag::NotBooleanConvertible);
    CHECK(diags[6].code == diag::EventExpressionFuncArg);
}

TEST_CASE("Conditional event control") {
    auto tree = SyntaxTree::fromText(R"(
module latch (output logic [31:0] y, input [31:0] a, input enable);
    always @(a iff enable == 1)
        y <= a;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Case statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    logic foo;
    int bar;
    string blah;
    struct { logic l; } sp;
    int unpacked [3];

    always begin : block
        case (9'(foo))
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
            default;
        endcase

        case ("asdf")
            "asdf": ;
            {"a", "sd"}: ;
            blah: ;
            8'd0: ; // not comparable
        endcase

        casex (foo)
            1'b0: ;
            1'd1: ;
            default;
        endcase

        casez (3.2)
            default;
        endcase // not integral

        casez (3'b1x1)
            3.2:; // not integral
        endcase

        casex (foo) inside  // inside not allowed with casex
            1'b1, 1'bx: ;
            default;
        endcase

        case (bar) inside
            1, 2, 3: ;
            unpacked: ;
            default;
        endcase
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& cs = compilation.getRoot()
                   .topInstances[0]
                   ->body.membersOfType<ProceduralBlockSymbol>()
                   .begin()
                   ->getBody()
                   .as<BlockStatement>()
                   .body.as<CaseStatement>();

    CHECK(cs.expr.type->toString() == "logic[8:0]");

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::BadSetMembershipType);
    CHECK(diags[1].code == diag::BadSetMembershipType);
    CHECK(diags[2].code == diag::NoCommonComparisonType);
    CHECK(diags[3].code == diag::NoCommonComparisonType);
    CHECK(diags[4].code == diag::BadSetMembershipType);
    CHECK(diags[5].code == diag::BadSetMembershipType);
    CHECK(diags[6].code == diag::CaseInsideKeyword);
}

TEST_CASE("Assertion statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    logic foo [3];

    initial begin
        assert (i > 0) i++; else i--;
        assume #0 (i < 0) else bar();
        assume #0 (i < 0);
        cover final (i != 0) bar();

        assert (foo);                           // not boolean
        cover (i != 0) else $fatal(1, "SDF");   // fail stmt not allowed
    end

    function void bar(); endfunction
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
    CHECK(diags[0].code == diag::ConstEvalAssertionFailed);
}

TEST_CASE("Deferred assertion error cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function void f1; endfunction
    function void f2(int i, output int o); endfunction
    function automatic void f3(int i, ref r); endfunction
    function int error_code(); return (0); endfunction

    int i;
    string s;
    initial begin
        automatic logic r;
        assume #0 (i < 0) i++; else f1();
        assert #0 (i < 0) void'($bits(i));
        assert #0 (i < 0) f2(i, i);
        assert #0 (i < 0) f3(i, r);
        assert #0 (i < 0) $swrite(s, "%d", i);
        assert #0 (i < 0) error_code();
        assert #0 (i < 0) void'(error_code());
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::InvalidDeferredAssertAction);
    CHECK(diags[1].code == diag::DeferredAssertNonVoid);
    CHECK(diags[2].code == diag::DeferredAssertOutArg);
    CHECK(diags[3].code == diag::DeferredAssertAutoRefArg);
    CHECK(diags[4].code == diag::DeferredAssertOutArg);
    CHECK(diags[5].code == diag::UnusedResult);
}

TEST_CASE("Break statement check -- regression") {
    auto tree = SyntaxTree::fromText(R"(
module foo;
    always_comb
        for(int p = 0; p < 4; p++) begin
            automatic int bar;
            break;
        end

    always_comb
        for(int p = 0; p < 4; p++) begin
            begin
                automatic int bar;
                break;
            end
        end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
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
    CHECK(diags[0].code == diag::RepeatNotNumeric);
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
        while (foo > 0) begin
        end
        return 1;
    endfunction

    function int func4();
        do begin end while (foo > 0);
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
    CHECK(diags[0].code == diag::ValueOutOfRange);
    CHECK(diags[1].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
    CHECK(diags[2].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
    CHECK(diags[3].code == diag::ConstEvalFunctionIdentifiersMustBeLocal);
}

TEST_CASE("Local statement parameter") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    always begin: asdf
        localparam i = 1;
        parameter j = 2;
        static logic [i+3:j] foo = '1;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& foo = compilation.getRoot().lookupName<VariableSymbol>("m.asdf.foo");
    CHECK(foo.getType().getFixedRange() == ConstantRange{4, 2});
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
    int baz[];
    initial begin
        if (n >= 0) begin
            j = foo[n];
        end else begin
            j = foo[n];
        end

        if (baz) begin end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::IndexOOB);
    CHECK(diags[1].code == diag::NotBooleanConvertible);
}

TEST_CASE("Nonblocking assignment statement") {
    auto tree = SyntaxTree::fromText(R"(
module m;

    int j;
    bit g;
    initial begin
        j <= 2;
        g = j <= 2;
    end

endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Intra-assignment timing controls") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int j;
    int g;
    initial begin
        j <= #2 2;
        g = @(posedge j[0]) 3;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Intra-assignment timing control errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int j;
    int g;
    initial begin
        j <= (#2 2);
        g = 1 + #2 2;
    end

    localparam int i = foo();
    function int foo;
        int j;
        j = #2 2;
        return j;
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::TimingControlNotAllowed);
    CHECK(diags[1].code == diag::TimingControlNotAllowed);
    CHECK(diags[2].code == diag::ConstEvalTimedStmtNotConst);
    CHECK(diags[3].code == diag::TimingInFuncNotAllowed);
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

    auto& m = compilation.getRoot().lookupName<InstanceSymbol>("m").body;
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

TEST_CASE("Parallel blocks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial fork
        static int i = 4;
        i += 2;
    join

    int j = 0;
    initial begin
        begin end
        fork : bar
            j = 1;
            j = 2;
        join_any
        fork : foo
        join_none
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parallel blocks -- invalid in constexpr") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo;
        automatic int i = 0;
        fork : asdf
            i += 2;
        join_none
        return i;
    endfunction

    localparam int bar = foo();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalParallelBlockNotConst);
}

TEST_CASE("Statement blocks -- decl after statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        i++;
        int i;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::DeclarationsAtStart);
}

TEST_CASE("Void-casted function call statement") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function foo;
    endfunction

    initial begin
        void'(foo());
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Void-casted function call statement -- diags") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo;
    endfunction

    function void bar;
    endfunction

    int i = 4;
    initial begin
        void'(1 + 2);
        i = void'(3);
        void'(bar());
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::VoidCastFuncCall);
    CHECK(diags[1].code == diag::VoidNotAllowed);
    CHECK(diags[2].code == diag::BadCastType);
    CHECK(diags[3].code == diag::PointlessVoidCast);
}

TEST_CASE("Function call -- ignored return") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    function int foo;
        return 0;
    endfunction

    initial begin
        foo();
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedResult);
}

TEST_CASE("Else statement with implicit for loop block") {
    auto tree = SyntaxTree::fromText(R"(
interface Iface;
    logic foo;
endinterface

module m(Iface i);
    always begin
        if (i.foo) begin
        end
        else begin
            for (int i = 0; i < 10; i++) begin
            end
        end

        for (int i = 0; i < 5; i++) begin
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Disable / wait fork statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        disable fork;
        wait fork;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Wait statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a, b;
    int foo[3];
    initial begin
        wait (1) begin : asdf
            automatic int i = 1;
            i++;
        end
        wait (foo) a += b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NotBooleanConvertible);
}

TEST_CASE("Lifetimes of nested statement blocks") {
    auto tree = SyntaxTree::fromText(R"(
module automatic m;
    function automatic int func1;
        int i = 4;
        for (int j = 0; j < 10; j++) begin
            int k = j + i;
            i = j + k;
        end
        return i;
    endfunction

    function int func2;
        int i = 4;
        for (int j = 0; j < 10; j++) begin
            int k = j + i;
            i = j + k;
        end
        return i;
    endfunction

    localparam int p1 = func1();
    localparam int p2 = func2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("System functions that can also be tasks") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        automatic int i = $system("sdf");
        $system("blah");
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Event triggering statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    event e;
    event arr[3];
    initial begin
        -> e;
        ->> #3 e;
        -> arr[1];
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("wait_order statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    event a, b, c;
    initial begin
        wait_order(a, b, c);
        wait_order(a, b, c) else $display("foo!");
        wait_order(a, b, c) $display("bar!");
        wait_order(a, b, c) $display("bar!"); else $display("foo!");
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Repeat event controls") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic clk;
    int a;
    int foo[3];
    initial begin
        a = repeat (3) @(clk) a + 1;
        a = repeat (3) ;
        a = repeat (foo) @(clk) a + 1;
        a = repeat (3) #4 a + 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::RepeatControlNotEvent);
    CHECK(diags[1].code == diag::ExpectedExpression);
    CHECK(diags[2].code == diag::RepeatNotNumeric);
    CHECK(diags[3].code == diag::RepeatControlNotEvent);
}

TEST_CASE("Procedural assign / deassign statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a;
    wire b;
    int c;
    initial begin
        assign a = 5;
        deassign a;
        force b = 1;
        release b;
        force c = 4;
        release c;
    end

    assign c = 1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Procedural assign / deassign errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    logic l[3];
    wire [2:0] w;

    nettype int nt;
    nt x;

    initial begin
        automatic int q;
        assign l[0] = 1;
        deassign {i, l[0]};
        force {w[1], i[1]} = 1;
        release i[1];
        force {w[1], x} = 1;
        assign q = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::BadProceduralAssign);
    CHECK(diags[1].code == diag::BadProceduralAssign);
    CHECK(diags[2].code == diag::BadProceduralForce);
    CHECK(diags[3].code == diag::BadProceduralForce);
    CHECK(diags[4].code == diag::BadForceNetType);
    CHECK(diags[5].code == diag::AutoFromNonProcedural);
}

TEST_CASE("Unexpected port decls") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        input i;
    end

    function void bar;
        begin
            input k;
        end
    endfunction
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnexpectedPortDecl);
    CHECK(diags[1].code == diag::UnexpectedPortDecl);
}

TEST_CASE("fork-join return") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    task wait_20;
        fork
            # 20;
            return; // Illegal: cannot return; task lives in another process
        join_none
    endtask
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ReturnInParallel);
}

TEST_CASE("Statement restrictions inside functions") {
    auto tree = SyntaxTree::fromText(R"(
event a, b, c;
task t; endtask
function f;
    int i;
    i = #1 3;
    @(posedge i) i = 1;
    fork
        static int j = i;
        i++;
    join_any
    wait (i != 0) i = 1;
    wait_order(a, b, c);
    t();
endfunction

function g;
    int i;
    begin
        static int j = i;
        t();
    end
    fork
        begin
            int q;
    	    t();    // this is ok inside a fork-join_none
        end
        fork
            static int z = i;
            z++;
            t();
        join_any
        t();
    join_none
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[1].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[2].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[3].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[4].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[5].code == diag::TaskFromFunction);
    CHECK(diags[6].code == diag::TaskFromFunction);
}

TEST_CASE("Statement restrictions inside final blocks") {
    auto tree = SyntaxTree::fromText(R"(
task t; endtask
module m;
    final begin
        int i;
        i = #1 3;
        @(posedge i) i = 1;
        fork join_any
        t();
        wait fork;
        expect(i == 0);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[1].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[2].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[3].code == diag::TaskFromFinal);
    CHECK(diags[4].code == diag::TimingInFuncNotAllowed);
    CHECK(diags[5].code == diag::TimingInFuncNotAllowed);
}

TEST_CASE("Non-blocking timing control reference to auto") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        automatic int i;
        int j;
        j <= #i 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::AutoFromNonBlockingTiming);
}

TEST_CASE("Clocking block as event control") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    wire clk;
    clocking cb @clk;
        input clk;
    endclocking

    int i;
    initial begin
        @cb i++;
        @(cb) i++;
        @(cb or posedge cb) i++;
        @(cb.clk) i++;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ClockingBlockEventEdge);
}

TEST_CASE("Cycle delay errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    real r;
    initial begin
        ##r i = 1;
        ##1 i = 1;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ExprMustBeIntegral);
    CHECK(diags[1].code == diag::NoDefaultClocking);
}

TEST_CASE("Cycle delay in interface") {
    auto tree = SyntaxTree::fromText(R"(
interface intf(
    input clk
);

    default clocking cb @(posedge clk);
    endclocking

    task zeroDelay();
        ##0;
    endtask

endinterface
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Synchronous drives") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    wire clk;
    default clocking cb @clk;
        output i;
        input a = i;
    endclocking

    initial begin
        cb.i <= 1;
        cb.a <= 2;
        cb.i = 3;

        cb.i <= #3 1;   // bad
        cb.i[1] <= ##3 1'b1;  // ok

        i <= ##3 1; // bad
        {cb.i, cb.i[1]} <= 3; // bad
    end

    int j;
    assign j = 1;

    clocking cb2 @clk;
        output j;
    endclocking

    assign cb2.j = 3;

    int k = cb.i;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::WriteToInputClockVar);
    CHECK(diags[1].code == diag::ClockVarSyncDrive);
    CHECK(diags[2].code == diag::ClockVarBadTiming);
    CHECK(diags[3].code == diag::CycleDelayNonClock);
    CHECK(diags[4].code == diag::ClockVarAssignConcat);
    CHECK(diags[5].code == diag::ClockVarTargetAssign);
    CHECK(diags[6].code == diag::ClockVarSyncDrive);
    CHECK(diags[7].code == diag::ClockVarOutputRead);
}

TEST_CASE("Invalid case statement regress GH #422") {
    auto tree = SyntaxTree::fromText(R"(
initial casez       matches
       a
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Just check no assertion.
    compilation.getAllDiagnostics();
}

TEST_CASE("randcase statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[];
    initial begin
        byte a, b, x;
        randcase
            a + b : x = 1;
            a - b : x = 2;
            a ^ ~b : x = 3;
            12'h800 : x = 4;
            foo : x = 5;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExprMustBeIntegral);
}

TEST_CASE("randsequence statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int a;
    int cnt;

    initial begin
        randsequence (main)
            main : first second done ;
            first : add("foo") | dec ;
            second : pop | push ;
            done : { $display("done"); return; } ;
            add(string s) : { $display(s); } ;
            dec : { begin : foo $display("dec"); break; end } ;
            pop : repeat($urandom_range( 2, 6 )) push;
            push : if (1) done else pop | rand join (0.5) first second done;
            baz : case (a & 7) 1, 2: push; 3: pop; default done; endcase;
        endsequence

        randsequence( bin_op )
            void bin_op : value operator value // void type is optional
            { $display("%s %b %b", operator, value[1], value[2]); }
            ;
            bit [7:0] value : { return 8'($urandom); } ;
            string operator : add := 5 { return "+" ; }
                            | dec := 2 { return "-" ; }
                            | mult := 1 { return "*" ; }
            ;
            add : { $display("add"); };
            dec : { $display("dec"); };
            mult : { $display("mult"); };
        endsequence

        randsequence( A )
            void A : A1 A2;
            void A1 : { cnt = 1; } B repeat(5) C B
            { $display("c=%d, b1=%d, b2=%d", C, B[1], B[2]); }
            ;
            void A2 : if (a != 0) D(5) else D(20)
            { $display("d1=%d, d2=%d", D[1], D[2]); }
            ;
            int B : C { return C;}
                  | C C { return C[2]; }
                  | C C C { return C[3]; }
            ;
            int C : { cnt = cnt + 1; return cnt; };
            int D (int prm) : { return prm; };
        endsequence
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("randsequence errors") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int baz[];
    initial begin
        randsequence (main)
            main : first foo | rand join (baz) first first;
            first : if (baz) main := baz { $display("SDF"); } | repeat (baz) main;
            int bar(string first) : first;
            boz : bar bar("asdf") { $display(bar[0]); };
        endsequence

        randsequence()
            foo (string s) : { $display(s); };
        endsequence
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
    CHECK(diags[1].code == diag::RandJoinNotNumeric);
    CHECK(diags[2].code == diag::NotBooleanConvertible);
    CHECK(diags[3].code == diag::ExprMustBeIntegral);
    CHECK(diags[4].code == diag::ExprMustBeIntegral);
    CHECK(diags[5].code == diag::NotAProduction);
    CHECK(diags[6].code == diag::TooFewArguments);
    CHECK(diags[7].code == diag::IndexOOB);
    CHECK(diags[8].code == diag::TooFewArguments);
}

TEST_CASE("foreach loop non-standard syntax") {
    auto tree = SyntaxTree::fromText(R"(
module top;
    int array[8][8];
    initial begin
        foreach (array[i]) begin
            foreach (array[i][j]) begin
                array[i][j] = i * j;
            end
        end
    end
endmodule

class A;
    int subhash[string];
endclass
class C;
    A hash[string];
    task t(string index);
        foreach (hash[index].subhash[i]) begin
        end
    endtask
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NonstandardForeach);
}

TEST_CASE("for loop expression error checking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    initial begin
        for (i; ; i) begin end
        for (int j; j < 10; j++) begin end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::InvalidForInitializer);
    CHECK(diags[1].code == diag::InvalidForStepExpression);
    CHECK(diags[2].code == diag::InitializerRequired);
}

TEST_CASE("Additional statement block items") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    initial begin
        let a(x) = 1 + x;
        nettype int nt;
        i = a(3);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unrollable for loop drivers") {
    auto tree = SyntaxTree::fromText(R"(
 module m;
    int foo[10];
    initial
        for (int i = 1; i < 10; i += 2) begin : baz
            foo[i] = 2;
        end

    for (genvar i = 0; i < 10; i += 2) begin
        always_comb foo[i] = 1;
    end

    always_comb foo[1] = 1; // error

    struct { int foo; int bar; } baz[3][2];
    initial begin
        while (1) begin
            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 2; j++) begin
                    forever begin
                        if (i != 2 || j != 1)
                            #1 baz[i][j].foo = 1;
                    end
                end
            end
        end
    end
    for (genvar i = 0; i < 3; i++) begin
        always_comb baz[i][0].bar = 3;
    end

    always_comb baz[1][1].foo = 4; // error
    always_comb baz[1][1].bar = 4;
    always_comb baz[2][1].foo = 3;

    struct { int foo; int bar; } arr[21474836];
    initial begin
        for (int i = 0; i < 2147483647; i++) begin
            arr[i].foo = 1;
        end
    end
    always_comb arr[0].bar = 2;
 endmodule
)");

    CompilationOptions options;
    options.maxConstexprSteps = 10000;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Unrollable for loop drivers -- strict checking") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo[10];
    initial
        for (int i = 1; i < 10; i += 2) begin : baz
            foo[i] = 2;
        end

    for (genvar i = 0; i < 10; i += 2) begin
        always_comb foo[i] = 1;
    end
endmodule
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::StrictDriverChecking;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("foreach shadowed variable regression") {
    auto tree = SyntaxTree::fromText(R"(
class C #(parameter type foo_t);
    foo_t arr[];

    function void baz;
        foreach (arr[i]) begin
            for (int i = 0; i < 10; i++) begin
                if (i == 4)
                    break;
            end
        end
    endfunction
endclass

module m;
    C #(int) c;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Empty body warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    bit done = 0;
    int arr[];
    initial begin
        if (1);
        if (1); else;

        for (int i = 0; i < 10; i++); begin end

        repeat (1);
        forever;

        while (done == 0);
        begin
            done = 1;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::EmptyBody);
    CHECK(diags[1].code == diag::EmptyBody);
    CHECK(diags[2].code == diag::EmptyBody);
    CHECK(diags[3].code == diag::EmptyBody);
    CHECK(diags[4].code == diag::EmptyBody);
    CHECK(diags[5].code == diag::EmptyBody);
}

TEST_CASE("Conditional statement / expression pattern matching") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    localparam int foo = 2;
    int unsigned e, j;
    initial begin
        if (e matches foo &&& j > 0 &&& e matches .* &&& e matches .baz &&& baz > 2) begin
            j = baz;
        end
        else begin
            // Can't reference pattern var here.
            j = baz;
        end
    end

    typedef union tagged {
        struct {
            bit [4:0] reg1, reg2, regd;
        } Add;
        union tagged {
            bit [9:0] JmpU;
            struct {
                bit [1:0] cc;
                bit [9:0] addr;
            } JmpC;
        } Jmp;
    } Instr;

    Instr instr;
    initial begin
        if (instr matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))) begin
            j = 10'(c) + a;
        end

        if (instr matches (tagged Jmp .j) &&&
            j matches (tagged JmpC '{cc:.c,addr:.a})) begin
            e = 10'(c) + a;
        end
    end

    initial begin
        e = instr matches tagged Jmp tagged JmpC '{cc:.c,addr:.a} &&& foo > 1 ? 32'(a + 10'(c)) : 0;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Case statement pattern matching") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef union tagged {
        void Invalid;
        int Valid;
    } VInt;

    VInt v;
    initial begin
        case (v) matches
            tagged Invalid : $display ("v is Invalid");
            tagged Valid .n : $display ("v is Valid with value %d", n);
        endcase
    end

    typedef union tagged {
        struct {
            bit [4:0] reg1, reg2, regd;
        } Add;
        union tagged {
            bit [9:0] JmpU;
            struct {
                bit [1:0] cc;
                bit [9:0] addr;
            } JmpC;
        } Jmp;
    } Instr;

    int rf[];
    bit [9:0] pc;

    Instr instr;
    initial begin
        case (instr) matches
            tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
            tagged Jmp .j : case (j) matches
                                tagged JmpU .a : pc = pc + a;
                                tagged JmpC '{.c, .a}: if (rf[c] != 0) pc = a;
                            endcase
        endcase

        case (instr) matches
            tagged Add '{.*, .*, 0} : ; // no op
            tagged Add '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
            tagged Jmp .j : case (j) matches
                                tagged JmpU .a : pc = pc + a;
                                tagged JmpC '{.c, .a} : if (rf[c] != 0) pc = a;
                            endcase
        endcase

        case (instr) matches
            tagged Add .s: case (s) matches
                                '{.*, .*, 0} : ; // no op
                                '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                          endcase
            tagged Jmp .j: case (j) matches
                                tagged JmpU .a : pc = pc + a;
                                tagged JmpC '{.c, .a} : if (rf[c] != 0) pc = a;
                                default: begin end
                           endcase
        endcase

        case (instr) matches
            tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
            tagged Jmp (tagged JmpU .a) : pc = pc + a;
            tagged Jmp (tagged JmpC '{.c, .a}) : if (rf[c] != 0) pc = a;
        endcase

        case (instr) matches
            tagged Add '{reg2:.r2,regd:.rd,reg1:.r1} &&& (rd != 0):
                                                        rf[rd] = rf[r1] + rf[r2];
            tagged Jmp (tagged JmpU .a) : pc = pc + a;
            tagged Jmp (tagged JmpC '{addr:.a,cc:.c}) : if (rf[c] != 0) pc = a;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Pattern case statement invalid filter") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int foo;
    int bar[];
    initial begin
        case (foo) matches
            .* &&& bar: begin end
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NotBooleanConvertible);
}

TEST_CASE("Pattern matching -- fallback variable creation") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int bar;
    initial begin
        if (foo matches '{.a, tagged Jmp .b}) begin
            bar = a + b;
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndeclaredIdentifier);
}

TEST_CASE("Pattern matching error cases") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct { int a, b; } asdf;
    union tagged { int a; real b; } baz;
    initial begin
        if (asdf matches '{.c, .c}) begin end
        if (asdf matches tagged Foo) begin end
        if (baz matches tagged c) begin end
        if (baz matches tagged a tagged Foo) begin end
        if (baz matches '{.a, .b}) begin end
        if (asdf matches '{.a, .b, .c}) begin end
        if (asdf matches '{.a}) begin end
        if (asdf matches '{c: .*}) begin end
        if (asdf matches '{a: tagged Foo}) begin end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 9);
    CHECK(diags[0].code == diag::Redefinition);
    CHECK(diags[1].code == diag::PatternTaggedType);
    CHECK(diags[2].code == diag::UnknownMember);
    CHECK(diags[3].code == diag::PatternTaggedType);
    CHECK(diags[4].code == diag::PatternStructType);
    CHECK(diags[5].code == diag::PatternStructTooMany);
    CHECK(diags[6].code == diag::PatternStructTooFew);
    CHECK(diags[7].code == diag::UnknownMember);
    CHECK(diags[8].code == diag::PatternTaggedType);
}

TEST_CASE("Break / continue in fork join") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int bar;
    initial begin
        for (int i = 0; i < 10; i++) begin
            fork
                if (i == 0)
                    break;
                continue;
            join
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::StatementNotInLoop);
    CHECK(diags[1].code == diag::StatementNotInLoop);
}

TEST_CASE("Implicit call in recursive function") {
    auto tree = SyntaxTree::fromText(R"(
class Packet;
	bit [3:0] command;
	integer status;

	function integer current_status();
		current_status = status;
	endfunction

	int incr = 0;

	function integer update_status();
		update_status = status;
		if (incr < 2) begin
			incr = incr + 1;
			update_status;
		end

		if (update_status == 0)
			if (this.update_status != 0)
				command[update_status] = 1'b0;
		return update_status;
	endfunction
endclass
)");

    CompilationOptions options;
    options.flags |= CompilationFlags::AllowRecursiveImplicitCall;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedResult);
}

TEST_CASE("Ref args in fork-join blocks") {
    auto options = optionsFor(LanguageVersion::v1800_2023);
    auto tree = SyntaxTree::fromText(R"(
function automatic foo(ref a, ref static b);
    fork
        automatic int k = a;
        begin : foo
            $display(a);
            $display(b);
        end
    join_none
endfunction
)",
                                     options);

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RefArgForkJoin);
}

TEST_CASE("Pattern variable lookup from nested initializers") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    initial begin
        if (i matches .a) begin
            begin
                automatic int b = a;
            end
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Conditional statement with pattern and explicit block crash regress") {
    auto tree = SyntaxTree::fromText(R"(
always begin union instr:if(instr matches begin c T i:
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
}
