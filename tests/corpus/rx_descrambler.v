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
 *  Module name: rx_descrambler
 *
 * Scrambler Logic (HMC Spec version 1.0)
 * This module implements a parallel scrambler based on the
 * polynomial 1+ x^(-14) + x^(-15).
 *
 * Such Scrambler is typically shown as a 15 bit Linear Feedback Shift Register
 * (LFSR) with bits shifting from register 1 on the left to register 15 on the
 * right, with register 14 and 15 combining to shift into register 1.
 * The HMC Serializer outputs data[0] first from parallel tx data[n:0],
 * so if data[n:0] is to be bitwise scrambled with LFSR[n:0], we need the LFSR
 * to shift from n -> 0, the opposite direction from the typical illustration.
 * This implementation shifts data from LFSR[14] on the left to LFSR[0] on the
 * right, with LFSR[1] and [0] combining to shift into LFSR[14]. This way
 * LFSR[14:0] can bitwise scramble data[14:0] and be compatible with serializ-
 * ation that shifts out on the data[0] side.
 * Put otherwise: Polynomial 1+ x^(-14) + x^(-15) is equiv to
 * x^15 + x^1 + x^0
 *
 * This parallelized version calculates the next DWIDTH steps of values for
 * the LFSR.  These bits are used to scramble the parallel input, and to
 * choose the next value of lfsr (lfsr_steps[DWIDTH-1]).
 *
 * This is the descrambler.  It is self-seeding.  When lock is asserted it has
 * successfully found the correct value for the LFSR.  It is only implemented
 * for DWIDTH > 14.
 *
 * Since we know that scrambled zeros are being translated, we can calculate
 * what the seed will be in the next timestep.  In order to simplify the
 * calculation, we assume that the top bit is a one.  That has the happy side-
 * effect of letting us know that the seed didn't get stuck at all zeros.
 *
 * After the scrambler is locked, the input word may need to be aligned.  The
 * bit_slip input allows the scrambler to shift one bit with the serializer
 * to keep the scrambler in sync.
 */

`default_nettype none

module rx_descrambler #(
    parameter DWIDTH=16,
    parameter BITSLIP_SHIFT_RIGHT=1
)
(
    input wire              clk,
    input wire              res_n,
    input wire              bit_slip,
    input wire              can_lock,
    output reg              locked,
    input wire [DWIDTH-1:0] data_in,
    output reg [DWIDTH-1:0] data_out
    
);

reg  [14:0]       lfsr;                    // LINEAR FEEDBACK SHIFT REGISTER
wire [14:0]       lfsr_slipped;            // Temporary lfsr for bitslip
wire [14:0]       lfsr_steps [DWIDTH-1:0]; // LFSR values for serial time steps
wire [14:0]       calculated_seed;
wire [DWIDTH-1:0] data_out_tmp;

generate
    if(BITSLIP_SHIFT_RIGHT==1) begin
        assign lfsr_slipped = { (lfsr_steps[DWIDTH-1][1] ^ lfsr_steps[DWIDTH-1][0]) , lfsr_steps[DWIDTH-1][14:1] };
    end else begin
        assign lfsr_slipped = { lfsr_steps[DWIDTH-1][13:0], (lfsr_steps[DWIDTH-1][14] ^ lfsr_steps[DWIDTH-1][0])};
    end
endgenerate

`ifdef SIMULATION
    initial begin
       lfsr     <= 15'h0; 
    end
`endif

// SEQUENTIAL PROCESS
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    `ifdef RESET_ALL
        if(!res_n) begin
            data_out <= {DWIDTH {1'b0}};
            lfsr     <= 15'h0;
        end else 
    `endif
    begin
        data_out <= data_out_tmp;
        if (!locked) begin
            lfsr <= calculated_seed;
        end else begin
            if (bit_slip) begin
                lfsr <= lfsr_slipped;
            end else begin
                lfsr <= lfsr_steps[DWIDTH-1];
            end
        end    
    end

    if(!res_n) begin
        locked   <= 1'b0;
    end else begin
        if (!locked) begin
            if (calculated_seed == lfsr_steps[DWIDTH-1]) begin
                locked <= 1'b1;
            end
        end
        if(!can_lock) begin
            locked <= 1'b0;
        end
    end
end                 // serial shift right with left input

// SCRAMBLE

genvar j;
generate
    localparam OFFSET = DWIDTH-15; // It breaks here if DWIDTH < 15
    assign calculated_seed[14] = 1'b1; // Guess the top bit is 1

    // data_in is the past state of the LFSR, so we can figure out
    // the current value using a loop.

    for(j = 0; j < 14; j = j + 1) begin : seed_calc
        assign calculated_seed[j] = data_in[j+OFFSET] ^ data_in[j+OFFSET+1];
    end

    assign data_out_tmp [0] = data_in[0] ^ lfsr[0]; // single bit scrambled
    assign lfsr_steps[0]    = { (lfsr[1] ^ lfsr[0]) , lfsr[14:1] }; // lfsr at next bit clock
    for(j = 1; j < DWIDTH; j = j + 1) begin : scrambler_gen
        assign data_out_tmp[j] = data_in[j] ^ lfsr_steps[j-1][0];
        assign lfsr_steps[j]   = { (lfsr_steps[j-1][1] ^ lfsr_steps[j-1][0]) , lfsr_steps[j-1][14:1] };
    end
endgenerate

endmodule

`default_nettype wire

