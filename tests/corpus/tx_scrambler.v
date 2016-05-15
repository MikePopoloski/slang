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
 *  Module name: tx_scrambler
 *
 *  Description:
 *
 *  This module implements a parallel scrambler based on the
 *  polynomial 1+ x^(-14) + x^(-15).
 *  Such Scrambler is typically shown as a 15 bit Linear Feedback Shift Register
 *  (LFSR) with bits shifting from register 1 on the left to register 15 on the
 *  right, with register 14 and 15 combining to shift into register 1.
 *  The HMC Serializer outputs data[0] first from parallel tx data[n:0],
 *  so if data[n:0] is to be bitwise scrambled with LFSR[n:0], we need the LFSR
 *  to shift from n -> 0, the opposite direction from the typical illustration.
 *  This implementation shifts data from LFSR[14] on the left to LFSR[0] on the
 *  right, with LFSR[1] and [0] combining to shift into LFSR[14]. This way
 *  LFSR[14:0] can bitwise scramble data[14:0] and be compatible with serializ-
 *  ation that shifts out on the data[0] side.
 *  Put otherwise: Polynomial 1+ x^(-14) + x^(-15) is equiv to
 *  x^15 + x^1 + x^0
 *  This parallelized version calculates the next LANE_WIDTH steps of values for
 *  the LFSR.  These bits are used to scramble the parallel input, and to
 *  choose the next value of lfsr (lfsr_steps[LANE_WIDTH-1]).
 */

`default_nettype none

module tx_scrambler #(
    parameter LANE_WIDTH        = 16,
    parameter HMC_RX_AC_COUPLED = 1
)
(
    input wire              clk,
    input wire              res_n,
    input wire              disable_scrambler,
    input wire [14:0]       seed, // unique per lane
    input wire [LANE_WIDTH-1:0] data_in,
    output reg [LANE_WIDTH-1:0] data_out,
    input wire              rf_run_length_enable,
    output wire             rf_run_length_bit_flip
);

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================
wire [LANE_WIDTH-1:0]   data_out_tmp;
wire [LANE_WIDTH-1:0]   run_length_d_out;
reg  [14:0]             lfsr; // LINEAR FEEDBACK SHIFT REGISTER
wire [14:0]             lfsr_steps [LANE_WIDTH-1:0]; // LFSR values for serial time steps

// SEQUENTIAL PROCESS
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    `ifdef RESET_ALL
        if(!res_n) begin
            data_out <= {LANE_WIDTH{1'b0}};
        end else
    `endif
    begin
        data_out <= run_length_d_out;
    end

    if(!res_n) lfsr <= seed;
    else       lfsr <= disable_scrambler ? {15{1'b0}} : lfsr_steps[LANE_WIDTH-1];

end

// SCRAMBLE
genvar j;
generate

    assign data_out_tmp [0] = data_in[0] ^ lfsr[0]; // single bit scrambled.
    assign lfsr_steps[0]    = { (lfsr[1] ^ lfsr[0]) , lfsr[14:1] }; // lfsr at next bit clock
    for(j = 1; j < LANE_WIDTH; j = j + 1) begin : scrambler_gen
        assign data_out_tmp[j] = data_in[j] ^ lfsr_steps[j-1][0];
        assign lfsr_steps[j]   = { (lfsr_steps[j-1][1] ^ lfsr_steps[j-1][0]) , lfsr_steps[j-1][14:1] };
    end
endgenerate

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

generate
    if(HMC_RX_AC_COUPLED==1) begin

        tx_run_length_limiter #(
            .LANE_WIDTH(LANE_WIDTH)
        )
        run_length_limiter_I
        (
            .clk(clk),
            .res_n(res_n),
            .enable(rf_run_length_enable),
            .data_in(data_out_tmp),
            .data_out(run_length_d_out),
            .rf_bit_flip(rf_run_length_bit_flip)
        );
    end else begin
        assign rf_run_length_bit_flip = 1'b0;
        assign run_length_d_out = data_out_tmp;
    end
endgenerate

endmodule

`default_nettype wire

