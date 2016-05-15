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
 *  Module name: openhmc_ram
 *
 */

`default_nettype none

module openhmc_ram #(
        parameter DATASIZE  = 78,   // Memory data word width
        parameter ADDRSIZE  = 9,    // Number of memory address bits
        parameter PIPELINED = 0     
    ) (
        //----------------------------------
        //----SYSTEM INTERFACE
        //----------------------------------
        input wire                  clk,

        //----------------------------------
        //----Signals
        //----------------------------------
        input wire                  wen,
        input wire [DATASIZE-1:0]   wdata,
        input wire [ADDRSIZE-1:0]   waddr,
        input wire                  ren,
        input wire [ADDRSIZE-1:0]   raddr,
        output wire [DATASIZE-1:0]  rdata
    );

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

    wire [DATASIZE-1:0] rdata_ram;

    generate
        if (PIPELINED == 0)
        begin
            assign rdata    = rdata_ram;
        end
        else
        begin
            reg [DATASIZE-1:0]  rdata_dly;
            reg                 ren_dly;

            assign rdata    = rdata_dly;

            always @(posedge clk)
            begin
                ren_dly         <= ren;

                if (ren_dly)
                    rdata_dly   <= rdata_ram;
            end
        end
    endgenerate

    reg [DATASIZE-1:0]  MEM [0:(2**ADDRSIZE)-1];

    reg [DATASIZE-1:0]  data_out;

    assign rdata_ram = data_out;

    always @(posedge clk)
    begin
        if (wen)
            MEM[waddr]  <= wdata;
    end

    always @(posedge clk)
    begin
        if (ren)
            data_out    <= MEM[raddr];
    end

endmodule

`default_nettype wire
