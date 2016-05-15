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
 *  Module name: openhmc_counter48
 *
 */

`default_nettype none

module openhmc_counter48 #(
        parameter DATASIZE  = 16    // width of the counter, must be <=48 bits!
    ) (
        input wire                  clk,
        input wire                  res_n,
        input wire                  increment,
        input wire                  load_enable,
        output wire [DATASIZE-1:0]  value
);

    reg [DATASIZE-1:0]  value_reg;
    reg                 load_enable_reg;

    assign value    = value_reg;

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        if(!res_n) begin
            value_reg               <= {DATASIZE{1'b0}};
            load_enable_reg         <= 1'b0;
        end else begin
            load_enable_reg         <= load_enable;
            case ({load_enable_reg,increment})
                    2'b00:
                        value_reg   <= value_reg;
                    2'b01:
                        value_reg   <= (value_reg + 1'b1);
                    2'b10:
                        value_reg   <= {DATASIZE{1'b0}};
                    2'b11:
                        value_reg   <= {DATASIZE{1'b0}} + 1'b1;
            endcase
        end
    end

endmodule
`default_nettype wire