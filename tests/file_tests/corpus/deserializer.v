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
 */
module deserializer #(
	parameter LOG_DWIDTH=7,
	parameter DWIDTH=64
)
(
	input  wire 			clk,
	input  wire 			res_n,
	input  wire 			fast_clk,
	input  wire 			bit_slip,
	input  wire 			data_in,
	output wire [DWIDTH-1:0]data_out,
	input  wire 			lane_polarity
);

reg [DWIDTH-1:0] 	tmp_buffer;
reg [DWIDTH-1:0] 	buffer;
reg [DWIDTH-1:0] 	buffer2;
reg [DWIDTH-1:0] 	data_out_temp;
reg [LOG_DWIDTH-1:0]curr_bit = 'h0;
reg [5:0]			bit_slip_cnt;
reg 				bit_slip_done = 1'b0;

reg d_in_dly;

assign data_out = lane_polarity ? data_out_temp^{DWIDTH{1'b1}} : data_out_temp;

// SEQUENTIAL PROCESS
always @ (posedge fast_clk) begin
	if(!res_n) begin
		curr_bit 		<= {LOG_DWIDTH{1'b0}};
		bit_slip_done 	<= 1'b0;
	end else begin	
		
		#1ps d_in_dly <= data_in;

		if (!bit_slip || bit_slip_done) begin
			if(curr_bit == DWIDTH-1) begin
				curr_bit <= 0;
			end else begin
				curr_bit 	 <= curr_bit + 1;
			end
		end

		if (bit_slip && !bit_slip_done)
			bit_slip_done <= 1'b1;

		if (bit_slip_done && !bit_slip)
			bit_slip_done <= 1'b0;

		if (|curr_bit == 1'b0) begin
			buffer <= tmp_buffer;
		end
		tmp_buffer[curr_bit] <= d_in_dly;
 	end
end

always @ (posedge clk) begin
	if(!res_n) begin
		bit_slip_cnt <= 6'h0;
	end else begin
		if(bit_slip)
			bit_slip_cnt <= bit_slip_cnt + 1;

		buffer2 <= buffer;
		
		if(bit_slip_cnt < DWIDTH-1) begin
			data_out_temp <= buffer2;
		end else begin
			data_out_temp <= buffer;
		end
	end
end

endmodule

