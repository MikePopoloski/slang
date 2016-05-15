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
 *  Module name: openhmc_sync_fifo_reg_based
 *
 */

`default_nettype none

module openhmc_sync_fifo_reg_based #(
`ifdef CAG_ASSERTIONS
		parameter DISABLE_EMPTY_ASSERT		= 0,
		parameter DISABLE_FULL_ASSERT		= 0,
		parameter DISABLE_SHIFT_OUT_ASSERT	= 0,
		parameter DISABLE_XCHECK_ASSERT		= 0,
`endif
		parameter DWIDTH					= 8,
		parameter ENTRIES					= 4
	) (
		input wire				clk,
		input wire				res_n,
		input wire				shift_in,
		input wire				shift_out,
		input wire [DWIDTH-1:0]	d_in,

		output wire[DWIDTH-1:0] d_out,
		output reg				full,
		output reg				empty,
		output reg				almost_full,
		output reg				almost_empty
	);

	//the fifo_reg can currently only have up to 2047 entries
	localparam LG_ENTRIES =  (ENTRIES <= 2) ? 1 :
				(ENTRIES <= 4)    ?  2 :
				(ENTRIES <= 8)    ?  3 :
				(ENTRIES <= 16)   ?  4 :
				(ENTRIES <= 32)   ?  5 :
				(ENTRIES <= 64)   ?  6 : 7;

	reg [DWIDTH-1:0]	entry [0:ENTRIES-1];
	reg [LG_ENTRIES:0]	wp;

	integer				i;

	wire				shiftout_clean, shiftin_clean; 

	// first stage of fifo is output
	assign d_out				= entry[0];

	assign shiftout_clean	= shift_out && !empty;
	assign shiftin_clean	= shift_in  && !full;

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n) `else
always @(posedge clk) `endif
begin
		
	if(!res_n)	begin
		wp										<= {LG_ENTRIES+1 {1'b0}};
		full									<= 1'b0;
		empty									<= 1'b1;
		almost_empty							<= 1'b1;
		almost_full								<= 1'b0;
		`ifdef FULL_RES
			for (i=0; i<ENTRIES; i=i+1)
				entry[i]							<= {DWIDTH {1'b0}};
		`endif
	end else begin
		case ({shiftin_clean, shiftout_clean})
			2'b01: // only shift-out, move entries, decrement WP if not already 0 and check status signals
			begin
				for (i=1; i<ENTRIES; i=i+1)
					entry[i-1]					<= entry[i];

				if (|wp)
					wp							<= wp - 1'b1;

				empty							<= (wp == {{LG_ENTRIES {1'b0}}, 1'b1});
				full							<= 1'b0;
				almost_full						<= (wp >= ENTRIES+1-1);
				almost_empty					<= (wp < 1 + 2);
			end

			2'b10: // only shift-in, write at next free entry, increment WP and check status signals
			begin
				entry[wp[LG_ENTRIES-1:0]]		<= d_in;
				wp								<= wp + 1'b1;
				empty							<= 1'b0;
				full							<= (wp >= ENTRIES - 1);
				almost_full						<= (wp >= ENTRIES-1-1);
				almost_empty					<= (wp < 1);
			end

			2'b11: //simultaneous shift-in and -out, move entries through shift registers
			begin
				for (i=1; i<ENTRIES; i=i+1)
					entry[i-1]					<= entry[i];

				entry[wp[LG_ENTRIES-1:0]-1'b1]	<= d_in;
			end
			default: begin
			end
		endcase
	end
end	

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

	// when the FIFO signals empty, it must logically also be almost empty
	empty_means_aempty : assert property (@(posedge clk) disable iff(!res_n) empty |-> almost_empty);

	wp_eq_0_means_empty_A : assert property (@(posedge clk) disable iff(!res_n) (wp==0) |-> empty);
	wp_eq_0_means_empty_B : assert property (@(posedge clk) disable iff(!res_n) empty |-> (wp==0));

	aempty_condition_A : assert property (@(posedge clk) disable iff(!res_n) (wp>1) |-> !almost_empty);
	aempty_condition_B : assert property (@(posedge clk) disable iff(!res_n) !almost_empty |-> (wp>1));

	shift_in_and_full:			assert property (@(posedge clk) disable iff(!res_n) (shift_in |-> !full));

	if (DISABLE_SHIFT_OUT_ASSERT == 0)
		shift_out_and_empty:	assert property (@(posedge clk) disable iff(!res_n) (shift_out |-> !empty));

      if (DISABLE_XCHECK_ASSERT == 0)
	dout_known:					assert property (@(posedge clk) disable iff(!res_n) (!empty |-> !$isunknown(d_out)));


	final
	begin
		if (DISABLE_FULL_ASSERT == 0)
		begin
			assert_full_set:				assert (!full);
			assert_almost_full_set:			assert (!almost_full);
		end

		if (DISABLE_EMPTY_ASSERT == 0)
		begin
			assert_write_pointer_not_zero:	assert (wp == 0);
			assert_almost_empty_not_set:	assert (almost_empty);
			assert_empty_not_set:			assert (empty);
		end
	end
`endif // CAG_ASSERTIONS

endmodule

`default_nettype wire
