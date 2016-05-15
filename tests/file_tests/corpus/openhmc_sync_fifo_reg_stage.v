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
 *  Module name: openhmc_sync_fifo_reg_stage
 *
 */

`default_nettype none

module openhmc_sync_fifo_reg_stage #(parameter DWIDTH = 8)(
    input wire clk,
    input wire res_n,
    input wire [DWIDTH-1:0] d_in,
    input wire [DWIDTH-1:0] d_in_p,
    input wire p_full,  // full signal from the previous stage
    input wire n_full,  // full signal from the next stage
    input wire si,
    input wire so,
    output reg full,    // full = '1' -> this stage has a valid entry
    output reg [DWIDTH-1:0] d_out
);

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

wire en, muxi;

assign en = (si & so & full)                // so and si, shift through
            | (si & ~so & ~full && n_full)  // shift in new value
            | (~si & so & p_full);          // shift through

assign muxi = (si & ~so) | (si & so & ~p_full & full);

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------LOGIC STARTS HERE---------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

always @ (posedge clk or negedge res_n) begin
    if (!res_n) begin
        full <= 1'b0;
        d_out <= {DWIDTH{1'b0}};
    end else begin
        if (en) begin
            if (muxi) begin
                d_out <= d_in;      // enter new value when enabled
            end else begin
                d_out <= d_in_p;    // shift through
            end
        end

        full <= (full & si)             // stay full while si to other stage
                | (full & ~si & ~so)    // hold full
                | (~si & so & p_full)   // keep full as long as prev stage is full
                | (si & ~so & n_full);  // fill this stage by si
    end
end

endmodule

`default_nettype wire

