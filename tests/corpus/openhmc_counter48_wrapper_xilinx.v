/*
 *                              .--------------. .----------------. .------------.
 *                             | .------------. | .--------------. | .----------. |
 *                             | | ____  ____ | | | ____    ____ | | |   ______ | |
 *                             | ||_   ||   _|| | ||_   \  /   _|| | | .' ___  || |
 *       ___  _ __   ___ _ __  | |  | |__| |  | | |  |   \/   |  | | |/ .'   \_|| |
 *      / _ \| '_ \ / _ \ '_ \ | |  |  __  |  | | |  | |\  /| |  | | || |       | |
 *       (_) | |_) |  __/ | | || | _| |  | |_ | | | _| |_\/_| |_ | | |\ `.___.'\| |
 *      \___/| .__/ \___|_| |_|| ||____||____|| | ||_____||_____|| | | `._____.'| |
 *           | |               | |            | | |              | | |          | |
 *           |_|               | '------------' | '--------------' | '----------' |
 *                              '--------------' '----------------' '------------'
 *
 *  openHMC - An Open Source Hybrid Memory Cube Controller
 *  (C) Copyright 2014 Computer Architecture Group - University of Heidelberg
 *  www.ziti.uni-heidelberg.de
 *  B6, 26
 *  68159 Mannheim
 *  Germany
 *
 *  Contact: openhmc@ziti.uni-heidelberg.de
 *  http://ra.ziti.uni-heidelberg.de/openhmc
 *
 *   This source file is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This source file is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with this source file.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *  Module name: openhmc_counter48_wrapper_xilinx
 */

`default_nettype none

module openhmc_counter48_wrapper_xilinx #(
	    parameter DATASIZE	= 48,	 // width of the counter, must be <=48 bits!
	    parameter INC_SIZE	= 1,	 // must be <= 18bits
		parameter PIPELINED = 1
	) (
		input wire					clk,
		input wire					res_n,
		input wire	[INC_SIZE-1:0]	inc_value,
		output wire	[DATASIZE-1:0]	value
);

`ifdef SIMULATION
	initial
	begin
		if (DATASIZE > 48)
		begin
			$display ("unsupported DATASIZE parameter in counter48.\nMax value is 48, actual value is %2d", DATASIZE);
			$stop;
		end
	end
`endif

	wire [47:0]	value_w;

	DSP48E1 #(
		.ACASCREG(0),										// Number of pipeline registers between A/ACIN input and ACOUT output,
															// 0, 1, or 2
		.ADREG(PIPELINED),									// Number of pipeline registers on pre-adder output, 0 or 1
		.ALUMODEREG(PIPELINED),								// Number of pipeline registers on ALUMODE input, 0 or 1
		.AREG(0),											// Number of pipeline registers on the A input, 0, 1 or 2
		.AUTORESET_PATDET("NO_RESET"),						// NO_RESET, RESET_MATCH, RESET_NOT_MATCH
		.A_INPUT("DIRECT"),									// Selects A input used, "DIRECT" (A port) or "CASCADE" (ACIN port)
		.BCASCREG(PIPELINED),								// Number of pipeline registers between B/BCIN input and BCOUT output,
															// 0, 1, or 2
		.BREG(PIPELINED),									// Number of pipeline registers on the B input, 0, 1 or 2
		.B_INPUT("DIRECT"),									// Selects B input used, "DIRECT" (B port) or "CASCADE" (BCIN port)
		.CARRYINREG(1),										// Number of pipeline registers for the CARRYIN input, 0 or 1
		.CARRYINSELREG(1),									// Number of pipeline registers for the CARRYINSEL input, 0 or 1
		.CREG(0),											// Number of pipeline registers on the C input, 0 or 1
		.DREG(0),											// Number of pipeline registers on the D input, 0 or 1
		.INMODEREG(1),										// Number of pipeline registers on INMODE input, 0 or 1
		.MASK(48'h3fffffffffff),							// 48-bit Mask value for pattern detect
		.MREG(0),											// Number of multiplier pipeline registers, 0 or 1
		.OPMODEREG(1),										// Number of pipeline registers on OPMODE input, 0 or 1
		.PATTERN(48'h000000000000),							// 48-bit Pattern match for pattern detect
		.PREG(1),											// Number of pipeline registers on the P output, 0 or 1
		.SEL_MASK("MASK"),									// "C", "MASK", "ROUNDING_MODE1", "ROUNDING_MODE2"
		.SEL_PATTERN("PATTERN"),							// Select pattern value between the "PATTERN" value or the value on the
															// "C" port
		.USE_DPORT("FALSE"),								// Select D port usage, TRUE or FALSE
		.USE_MULT("NONE"),									// Select multiplier usage, "MULTIPLY", "DYNAMIC", or "NONE" (no multiplier)
		.USE_PATTERN_DETECT("NO_PATDET"),					// Enable pattern detect, "PATDET", "NO_PATDET"
		.USE_SIMD("ONE48")									// SIMD selection, "ONE48", "TWO24", "FOUR12"
	) DSP48E1_inst (
		// Cascade: 30-bit (each) Cascade
		.ACOUT(),											// 30-bit A port cascade output
		.BCOUT(),											// 18-bit B port cascade output
		.CARRYCASCOUT(),									// 1-bit cascade carry output
		.MULTSIGNOUT(),										// 1-bit multiplier sign cascade output
		.PCOUT(),											// 48-bit cascade output
															// Control: 1-bit (each) Control
		.OVERFLOW(),										// 1-bit overflow in add/acc output
		.PATTERNBDETECT(),									// 1-bit active high pattern bar detect output
		.PATTERNDETECT(),									// 1-bit active high pattern detect output
		.UNDERFLOW(),										// 1-bit active high underflow in add/acc output
		// Data: 4-bit (each) Data
		.CARRYOUT(),										// 4-bit carry output
		.P(value_w),										// 48-bit output
															// Cascade: 30-bit (each) Cascade
		.ACIN(30'b0),										// 30-bit A cascade data input
		.BCIN(18'b0),										// 18-bit B cascade input
		.CARRYCASCIN(1'b0),									// 1-bit cascade carry input
		.MULTSIGNIN(1'b0),									// 1-bit multiplier sign input
		.PCIN(48'b0),										// 48-bit P cascade input
															// Control: 4-bit (each) Control
		.ALUMODE(4'b0000),									// 4-bit ALU control input
		.CARRYINSEL(3'b000),								// 3-bit carry select input
		.CEINMODE(1'b0),									// 1-bit active high clock enable input for INMODE registers
		.CLK(clk),											// 1-bit Clock input
		.INMODE(5'b00000),									// 5-bit INMODE control input
		.OPMODE({1'b0, 1'b1, 1'b0, 4'b0011}),				// 7-bit operation mode input
		.RSTINMODE(!res_n),									// 1-bit reset input for INMODE pipeline registers
															// Data: 30-bit (each) Data
		.A(30'b0),											// 30-bit A data input
		.B({{18-INC_SIZE{1'b0}}, inc_value}),				// 18-bit B data input
		.C(48'h0),											// 48-bit C data input
		.CARRYIN(1'b0),										// 1-bit carry input signal
		.D(25'b0),											// 25-bit D data input
															// Reset/Clock Enable: 1-bit (each) Reset/Clock Enable
		.CEA1(1'b0),										// 1-bit active high clock enable input for 1st stage A registers
		.CEA2(1'b0),										// 1-bit active high clock enable input for 2nd stage A registers
		.CEAD(1'b0),										// 1-bit active high clock enable input for pre-adder output registers
		.CEALUMODE(1'b1),									// 1-bit active high clock enable input for ALUMODE registers
		.CEB1(1'b0),										// 1-bit active high clock enable input for 1st stage B registers
		.CEB2(1'b1),										// 1-bit active high clock enable input for 2nd stage B registers
		.CEC(1'b0),											// 1-bit active high clock enable input for C registers
		.CECARRYIN(1'b0),									// 1-bit active high clock enable input for CARRYIN register
		.CECTRL(1'b1),										// 1-bit active high clock enable input for OPMODE and carry registers
		.CED(1'b0),											// 1-bit active high clock enable input for D registers
		.CEM(1'b0),											// 1-bit active high clock enable input for multiplier registers
		.CEP(1'b1),											// 1-bit active high clock enable input for P registers
		.RSTA(1'b0),										// 1-bit reset input for A pipeline registers
		.RSTALLCARRYIN(1'b0),								// 1-bit reset input for carry pipeline registers
		.RSTALUMODE(1'b0),									// 1-bit reset input for ALUMODE pipeline registers
		.RSTB(!res_n),										// 1-bit reset input for B pipeline registers
		.RSTC(1'b0),										// 1-bit reset input for C pipeline registers
		.RSTCTRL(!res_n),									// 1-bit reset input for OPMODE pipeline registers
		.RSTD(1'b0),										// 1-bit reset input for D pipeline registers
		.RSTM(1'b0),										// 1-bit reset input for multiplier registers
		.RSTP(!res_n)										// 1-bit reset input for P pipeline registers
	);



generate
	if(PIPELINED==1) begin
		reg [DATASIZE-1:0] value_temp;
		always @(posedge clk) begin
			value_temp		<= value_w[DATASIZE-1:0];
		end
		assign value=value_temp;
	end else begin
		assign value	= value_w[DATASIZE-1:0];
	end
endgenerate

endmodule

`default_nettype wire
