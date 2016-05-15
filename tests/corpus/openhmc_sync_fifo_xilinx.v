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
 *  Module name: openhmc_sync_fifo_xilinx
 *
 */
 
`default_nettype none

module openhmc_sync_fifo_xilinx #(
`ifdef CAG_ASSERTIONS
		parameter DISABLE_EMPTY_ASSERT		= 0,
		parameter DISABLE_FULL_ASSERT		= 0,
		parameter DISABLE_SHIFT_OUT_ASSERT	= 0,
		parameter DISABLE_XCHECK_ASSERT		= 0,
`endif
		parameter DWIDTH					= 8
	) (
		input wire				clk,
		input wire				res_n,
		input wire [DWIDTH-1:0]	d_in,
		input wire				shift_in,
		input wire				shift_out,
		output reg [DWIDTH-1:0] d_out,
		output wire				full,
		output reg				empty,
		output wire				almost_full,
		output wire				almost_empty
	);

	wire [DWIDTH-1:0]	d_out_w;
	wire				empty_w;
	wire				shift_out_w;
	wire				shift_in_w;
	
		assign shift_out_w	= !empty_w && (empty || shift_out);
		assign shift_in_w	= shift_in;

		`ifdef ASYNC_RES
		always @(posedge clk or negedge res_n) `else
		always @(posedge clk ) `endif
		begin
			if (!res_n)
			begin
				empty		<= 1'b1;
				d_out		<= {DWIDTH {1'b0}};
			end
			else
			begin
				if (!empty_w && (empty || shift_out))
				begin
					d_out	<= d_out_w;
					empty	<= 1'b0;
				end
				else if (shift_out)
					empty	<= 1'b1;
			end
		end

	openhmc_srl_fifo_16 #(
		`ifdef CAG_ASSERTIONS
			.DISABLE_EMPTY_ASSERT(DISABLE_EMPTY_ASSERT),
			.DISABLE_FULL_ASSERT(DISABLE_FULL_ASSERT),
		`endif
		.DWIDTH(DWIDTH)
	) srl_fifo_I (
		.clk(clk),
		.res_n(res_n),
		.d_in(d_in),
		.d_out(d_out_w),
		.shift_out(shift_out_w),
		.shift_in(shift_in_w),
		.full(full),
		.almost_full(almost_full),
		.empty(empty_w),
		.almost_empty(almost_empty)
	);

`ifdef CAG_COVERAGE
	full_cov:				cover property (@(posedge clk) disable iff(!res_n) (full == 1'b1));
	almost_full_cov:		cover property (@(posedge clk) disable iff(!res_n) (almost_full == 1'b1));
	empty_cov:				cover property (@(posedge clk) disable iff(!res_n) (empty == 1'b1));
	almost_empty_cov:		cover property (@(posedge clk) disable iff(!res_n) (almost_empty == 1'b1));

	covergroup shift_in_and_out @(posedge clk);
		shift_in_and_out_cp: coverpoint ({shift_in, shift_out}) iff (shift_in || shift_out)
		{
			bins count[] = {[1:3]};
		}
	endgroup
	shift_in_and_out shift_in_and_out_I;
	initial begin
		shift_in_and_out_I = new();
		shift_in_and_out_I.set_inst_name("shift_in_and_out_I");
	end
`endif // CAG_COVERAGE

`ifdef CAG_ASSERTIONS
	shift_in_and_full:				assert property (@(posedge clk) disable iff(!res_n) (shift_in |-> !full));

	if (DISABLE_SHIFT_OUT_ASSERT == 0)
		shift_out_and_empty:		assert property (@(posedge clk) disable iff(!res_n) (shift_out |-> !empty));

	if (DISABLE_XCHECK_ASSERT == 0)
	  d_out_known:					assert property (@(posedge clk) disable iff(!res_n) (!empty |-> !$isunknown(d_out)));

	final
	begin
		if (DISABLE_FULL_ASSERT == 0)
		begin
			assert_full_set:				assert (!full);
			assert_almost_full_set:			assert (!almost_full);
		end

		if (DISABLE_EMPTY_ASSERT == 0)
		begin
			assert_almost_empty_not_set:	assert (almost_empty);
			assert_empty_not_set:			assert (empty);
		end
	end
`endif // CAG_ASSERTIONS

endmodule

`default_nettype wire
