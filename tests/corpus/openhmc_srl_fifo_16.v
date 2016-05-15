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
 *  Module name: openhmc_srl_fifo_16
 *
 */

`default_nettype none

module openhmc_srl_fifo_16 #(
`ifdef CAG_ASSERTIONS
		parameter DISABLE_EMPTY_ASSERT	= 0,
		parameter DISABLE_FULL_ASSERT	= 0,
`endif
		parameter DWIDTH				= 8
	) (
		input wire				clk,
		input wire				res_n,
		input wire [DWIDTH-1:0]	d_in,
		input wire				shift_in,
		input wire				shift_out,

		output wire [DWIDTH-1:0]d_out,
		output reg				full,
		output reg				empty,
		output reg				almost_full,
		output reg				almost_empty
	);

	reg [3:0]	count;
	wire		shift_out_notempty;
	wire		shift_in_notfull;

	genvar		i;

	assign shift_out_notempty	= (shift_out && !empty);
	assign shift_in_notfull		= (shift_in  && !full);

	generate
		for (i=0; i < DWIDTH; i=i+1)
		begin: generate_SRL16
			SRL16E #(.INIT(16'h0000)) SRL16_I (
				.Q(d_out[i]),	// SRL data output
				.A0(count[0]),	// Select[0] input
				.A1(count[1]),	// Select[1] input
				.A2(count[2]),	// Select[2] input
				.A3(count[3]),	// Select[3] input
				.CLK(clk),
				.D(d_in[i]),		// SRL data input
				.CE(shift_in_notfull)
			);
		end
	endgenerate

	`ifdef ASYNC_RES
	always @(posedge clk or negedge res_n) `else
	always @(posedge clk) `endif
	begin
		if (!res_n)
		begin
			count					<= 4'b0;
			full					<= 1'b0;
			almost_full				<= 1'b0;
			empty					<= 1'b1;
			almost_empty			<= 1'b1;
		end
		else
		begin
			case ({shift_in_notfull, shift_out_notempty})
				2'b00: ; // nothing to do
				2'b01:
				begin
					if (|count)
						count		<= count - 1'b1;
					empty			<= !(|count);
					almost_empty	<= (count <= 1);
					full			<= 1'b0;
					almost_full		<= (count > (4'd15 - 1));
				end
				2'b10:
				begin
					if (!empty)
						count		<= count + 1'b1;
					empty			<= 1'b0;
					almost_empty	<= empty;
					full			<= (count > 4'd13);
					almost_full		<= (count > (4'd13 - 1));
				end
				2'b11: ;
			endcase
		end
	end

`ifdef CAG_COVERAGE
	full_cov:			cover property (@(posedge clk) disable iff(!res_n) (full == 1'b1));
	almost_full_cov:	cover property (@(posedge clk) disable iff(!res_n) (almost_full == 1'b1));
	empty_cov:			cover property (@(posedge clk) disable iff(!res_n) (empty == 1'b1));
	almost_empty_cov:	cover property (@(posedge clk) disable iff(!res_n) (almost_empty == 1'b1));
`endif // CAG_COVERAGE

`ifdef CAG_ASSERTIONS
	final
	begin
		if (DISABLE_FULL_ASSERT == 0)
		begin
			full_set_assert: assert (!full);
			almost_full_set_assert:			assert (!almost_full);
		end

		if (DISABLE_EMPTY_ASSERT == 0)
		begin
			almost_empty_not_set_assert:	assert (almost_empty);
			empty_not_set_assert:			assert (empty);
		end
	end
`endif // CAG_ASSERTIONS

endmodule

`default_nettype wire