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
 *  Module name: tx_run_length_limiter
 *
 *  Description:
 *  The idea is to break the counts up into manageable chunks.  FPGAs have 6-input LUTs, so a
 *  reasonable granularity is 5.  This means that we check 5 bits + the previous bit in every chunk.
 *
 *  Granularity 1 should be more accurate, but uses more resources.
 *
 *  When there are no bit flips in the input, count_top and count_bottom should be equal.
 *  Calculating them separately is faster and uses fewer resources.
 */

`default_nettype none

module tx_run_length_limiter #(
    parameter LANE_WIDTH  =64,
    parameter GRANULARITY =4,
    parameter RUN_LIMIT   =85
)
(
    input wire              clk,
    input wire              res_n,
    input wire              enable,
    input wire [LANE_WIDTH-1:0] data_in,
    output reg [LANE_WIDTH-1:0] data_out,
    output reg              rf_bit_flip
);

localparam NUM_CHUNKS   = (LANE_WIDTH + GRANULARITY-1)/(GRANULARITY);
localparam REM_BITS     = LANE_WIDTH - (GRANULARITY * (LANE_WIDTH/GRANULARITY));
localparam COUNT_BITS   = 8;

wire [NUM_CHUNKS-1:0] no_flip;
wire [NUM_CHUNKS-1:0] still_counting_top;
wire [NUM_CHUNKS-1:0] still_counting_bottom;

wire [COUNT_BITS-1:0] count_top;
wire [COUNT_BITS-1:0] count_top_part    [NUM_CHUNKS-1:0];
wire [COUNT_BITS-1:0] count_bottom;
wire [COUNT_BITS-1:0] count_bottom_part [NUM_CHUNKS-1:0];

wire bit_flip;

reg [COUNT_BITS-1:0] count_bottom_d1;
reg                  no_flip_bottom_d1;
reg                  data_in_bottom_d1;

genvar chunk;
genvar chunkT;
genvar chunkB;
generate

    assign no_flip[0] = &( {data_in[GRANULARITY-1:0],data_in_bottom_d1}) ||
                        &(~{data_in[GRANULARITY-1:0],data_in_bottom_d1});

    for(chunk=1; chunk<NUM_CHUNKS-1; chunk=chunk+1) begin : no_flip_gen
        assign no_flip[chunk]    =  &( data_in[(chunk+1)*(GRANULARITY)-1:chunk*(GRANULARITY)-1]) ||
                                    &(~data_in[(chunk+1)*(GRANULARITY)-1:chunk*(GRANULARITY)-1]);
    end

    assign no_flip[NUM_CHUNKS-1] =  &( data_in[LANE_WIDTH-1:(NUM_CHUNKS-1)*(GRANULARITY)-1]) ||
                                    &(~data_in[LANE_WIDTH-1:(NUM_CHUNKS-1)*(GRANULARITY)-1]);


    // Start at the top and count until a flip is found
    assign still_counting_top[0] = no_flip[0];
    assign count_top_part[0]     = (no_flip[0] ? GRANULARITY : 0);

    for(chunkT=1; chunkT<NUM_CHUNKS; chunkT=chunkT+1) begin : count_top_gen
        assign still_counting_top[chunkT]   = still_counting_top[chunkT-1] && no_flip[chunkT];
        assign count_top_part[chunkT]       = (still_counting_top[chunkT] ? GRANULARITY : 0) + count_top_part[chunkT-1];
    end

    assign count_top = (still_counting_top[NUM_CHUNKS-1] ? LANE_WIDTH :             // No flips found
                        count_top_part[NUM_CHUNKS-2]) +                     // Take the last value
                        (no_flip[0] ? (count_bottom_d1 == 0 ? 1 : count_bottom_d1) : 0); // Add the saved count

    // Start at the bottom and count until a flip is found
    assign still_counting_bottom[0] = no_flip[NUM_CHUNKS-1];
    assign count_bottom_part[0]     = 0;

    for(chunkB=1; chunkB<NUM_CHUNKS; chunkB=chunkB+1) begin : count_bottom_gen
        assign still_counting_bottom[chunkB] = still_counting_bottom[chunkB-1] && no_flip[NUM_CHUNKS-1-chunkB];
        assign count_bottom_part[chunkB]     = (still_counting_bottom[chunkB] ? GRANULARITY : 0) + count_bottom_part[chunkB-1];
    end

    assign count_bottom = still_counting_bottom[NUM_CHUNKS-1] ? LANE_WIDTH + (count_bottom_d1 == 0 ? 1 : count_bottom_d1) : // No flips found + saved count
                          count_bottom_part[NUM_CHUNKS-2] +                                     // Take the last value
                          (no_flip[NUM_CHUNKS-1] ? (REM_BITS ? REM_BITS : GRANULARITY) + 1 : 0);    // Add the remainder

endgenerate

assign bit_flip = count_top > (RUN_LIMIT - (GRANULARITY-1) - (REM_BITS ? REM_BITS-1 : GRANULARITY-1));

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    `ifdef RESET_ALL
        if(!res_n) begin
            data_out <= {DWIDTH {1'b0}};
        end else 
    `endif
    begin
        if (enable && bit_flip) begin
            data_out    <= {data_in[LANE_WIDTH-1:1], ~data_in[0]};
        end else begin
            data_out    <= data_in;
        end
    end
    if (!res_n) begin
        count_bottom_d1   <= { COUNT_BITS {1'b0}};
        no_flip_bottom_d1 <= 1'b0;
        data_in_bottom_d1 <= 1'b0;
        rf_bit_flip       <= 1'b0;
    end else begin
        count_bottom_d1   <= count_bottom;
        no_flip_bottom_d1 <= no_flip[NUM_CHUNKS-1];
        data_in_bottom_d1 <= data_in[LANE_WIDTH-1];
        if (enable && bit_flip) begin
            rf_bit_flip <= bit_flip;
        end
    end
end

endmodule
