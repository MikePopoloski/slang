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
 *  Module name: rx_lane_logic
 *
 */

`default_nettype none

module rx_lane_logic #(
    parameter DWIDTH             = 512,
    parameter NUM_LANES          = 8,
    parameter LANE_DWIDTH        = (DWIDTH/NUM_LANES),
    parameter CTRL_LANE_POLARITY = 1,
    parameter BITSLIP_SHIFT_RIGHT= 1
) (

    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    input   wire clk,
    input   wire res_n,

    //----------------------------------
    //----CONNECT
    //----------------------------------
    input   wire [LANE_DWIDTH-1:0]      scrambled_data_in,
    input   wire                        bit_slip,   //bit slip per lane
    input   wire                        lane_polarity,
    input   wire                        can_lock,
    output  wire [LANE_DWIDTH-1:0]      descrambled_data_out,
    output  wire                        descrambler_locked,
    input   wire                        descrambler_disable

);

wire    [LANE_DWIDTH-1:0]       descrambled_data_out_tmp;
wire    [LANE_DWIDTH-1:0]       data_2_descrambler;
wire                            descrambler_locked_tmp;
assign descrambler_locked       = descrambler_disable ? can_lock : descrambler_locked_tmp;



//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------ACTUAL LOGIC STARTS HERE--------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================
generate 
    if(CTRL_LANE_POLARITY==1) begin

        reg [LANE_DWIDTH-1:0] scrambled_data_in_reg;

        `ifdef ASYNC_RES
        always @(posedge clk or negedge res_n)  begin `else
            always @(posedge clk)  begin `endif

            `ifdef RESET_ALL
            if(!res_n) begin
                scrambled_data_in_reg   <=  {LANE_DWIDTH{1'b0}};
            end else 
            `endif
            begin
                scrambled_data_in_reg   <= scrambled_data_in^{LANE_DWIDTH{lane_polarity}};
            end
        end

        assign data_2_descrambler   = scrambled_data_in_reg;
        assign descrambled_data_out = descrambler_disable ? scrambled_data_in_reg : descrambled_data_out_tmp;

    end else begin

        assign data_2_descrambler   = scrambled_data_in;
        assign descrambled_data_out = descrambler_disable ? scrambled_data_in : descrambled_data_out_tmp;

    end
endgenerate

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

//Descrambler Init
    rx_descrambler #(
        .DWIDTH(LANE_DWIDTH),
        .BITSLIP_SHIFT_RIGHT(BITSLIP_SHIFT_RIGHT)
    ) descrambler_I (
        .clk(clk),
        .res_n(res_n),
        .can_lock(can_lock),
        .bit_slip(bit_slip),
        .locked(descrambler_locked_tmp),
        .data_in(data_2_descrambler),
        .data_out(descrambled_data_out_tmp)
    );

endmodule
`default_nettype wire