// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"

TEST_CASE("NoLegacyGenerate: For loop inside generate block") {
    auto tree = SyntaxTree::fromText(R"(
module eq_n
	#( parameter N =4)
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
	generate begin : named_generate
		genvar i ;
		for ( i = 0; i < N ; i = i + 1)
			xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
	end
	endgenerate
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoLegacyGenerate");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoLegacyGenerate: For loop inside unnamed generate block") {
    auto tree = SyntaxTree::fromText(R"(
module eq_n
	#( parameter N =4)
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
	generate
		genvar i ;
		for ( i = 0; i < N ; i = i + 1)
			xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
	endgenerate
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoLegacyGenerate");
    bool result = visitor->check(root);
    CHECK_FALSE(result);
}

TEST_CASE("NoLegacyGenerate: For loop, no generate block") {
    auto tree = SyntaxTree::fromText(R"(
module eq_n
	#( parameter N =4)
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
    for (genvar i = 0; i < N ; i = i + 1)
        xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    auto& root = compilation.getRoot();

    TidyConfig config;
    Registry::setConfig(config);
    Registry::setSourceManager(compilation.getSourceManager());
    auto visitor = Registry::create("NoLegacyGenerate");
    bool result = visitor->check(root);
    CHECK(result);
}

TEST_CASE("NoLegacyGenerate: For loop inside conditional block") {
    auto tree = SyntaxTree::fromText(R"(
module eq_n
	#(
        parameter N = 4,
        parameter cond = 0
    )
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
    if (cond) begin
        for (genvar i = 0; i < N ; i = i + 1) begin : foo_name
            xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
        end
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
    auto visitor = Registry::create("NoLegacyGenerate");
    bool result = visitor->check(root);
    CHECK(result);
}
