// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("NoLegacyGenerate: For loop inside generate block") {
    auto result = runCheckTest("NoLegacyGenerate", R"(
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
    CHECK_FALSE(result);
}

TEST_CASE("NoLegacyGenerate: For loop inside unnamed generate block") {
    auto result = runCheckTest("NoLegacyGenerate", R"(
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
    CHECK_FALSE(result);
}

TEST_CASE("NoLegacyGenerate: For loop, no generate block") {
    auto result = runCheckTest("NoLegacyGenerate", R"(
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
    CHECK(result);
}

TEST_CASE("NoLegacyGenerate: For loop inside conditional block") {
    auto result = runCheckTest("NoLegacyGenerate", R"(
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
    CHECK(result);
}
