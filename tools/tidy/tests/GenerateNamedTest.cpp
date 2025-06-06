// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-FileCopyrightText: MIT

#include "Test.h"
#include "TidyFactory.h"
#include "TidyTest.h"

TEST_CASE("GenerateNamed: Unnamed generate block") {
    auto result = runCheckTest("GenerateNamed", R"(
module eq_n
	#( parameter N =4)
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
	generate begin
		genvar i ;
		for ( i = 0; i < N ; i = i + 1)
			xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
	end
	endgenerate

	assign eq = & tmp ;
endmodule

)");
    CHECK_FALSE(result);
}

TEST_CASE("GenerateNamed: Named generate block") {
    auto result = runCheckTest("GenerateNamed", R"(
module eq_n
	#( parameter N =4)
	(
		input logic [N -1:0] a , b ,
		output logic eq
	) ;
	logic [N -1:0] tmp ;
	generate begin : gen_named
		genvar i ;
		for ( i = 0; i < N ; i = i + 1)
			xnor gen_u ( tmp [ i ] , a [ i ] , b [ i ]) ;
	end
	endgenerate

	assign eq = & tmp ;
endmodule

)");
    CHECK(result);
}

TEST_CASE("GenerateNamed: Unnamed simple generate block") {
    auto result = runCheckTest("GenerateNamed", R"(
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

	assign eq = & tmp ;
endmodule

)");
    CHECK_FALSE(result);
}

TEST_CASE("GenerateNamed: Unnamed for block") {
    auto result = runCheckTest("GenerateNamed", R"(
module full_adder(
  input a, b, cin,
  output sum, cout
);

  assign {sum, cout} = {a^b^cin, ((a & b) | (b & cin) | (a & cin))};
endmodule

module ripple_carry_adder #(parameter SIZE = 4) (
  input [SIZE-1:0] A, B,
  input Cin,
  output [SIZE-1:0] S, Cout);

  full_adder fa0(A[0], B[0], Cin, S[0], Cout[0]);

  for(genvar g = 1; g<SIZE; g++) begin
    full_adder fa(A[g], B[g], Cout[g-1], S[g], Cout[g]);
  end
endmodule
)");
    CHECK_FALSE(result);
}

TEST_CASE("GenerateNamed: Named for block") {
    auto result = runCheckTest("GenerateNamed", R"(
module full_adder(
  input a, b, cin,
  output sum, cout
);

  assign {sum, cout} = {a^b^cin, ((a & b) | (b & cin) | (a & cin))};
endmodule

module ripple_carry_adder #(parameter SIZE = 4) (
  input [SIZE-1:0] A, B,
  input Cin,
  output [SIZE-1:0] S, Cout);

  full_adder fa0(A[0], B[0], Cin, S[0], Cout[0]);

  for(genvar g = 1; g<SIZE; g++) begin: foo
    full_adder fa(A[g], B[g], Cout[g-1], S[g], Cout[g]);
  end
endmodule
)");
    CHECK(result);
}
