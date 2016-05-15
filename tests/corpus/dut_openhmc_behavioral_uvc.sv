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

`default_nettype none
`timescale 100ps/1ps

module dut #(
    //*************************Don't touch! Control the design with arguments when executing run.sh
	parameter LOG_NUM_LANES             = `LOG_NUM_LANES,
    parameter NUM_LANES                 = 2**LOG_NUM_LANES,
    parameter LOG_FPW                   = `LOG_FPW,
    parameter FPW                       = `FPW,
    parameter DWIDTH                    = 128*FPW,
    parameter NUM_DATA_BYTES            = 16*FPW,
    parameter LANE_WIDTH                = DWIDTH / NUM_LANES
    //*************************
    )
    (
    //AXI4 user clock
    input wire clk_user,
    //125MHz reference clock
    input wire clk_hmc_refclk,
    //Global reset
    input wire res_n,

    //HMC Link interface
    hmc_sr_if hmc,
    //AXI4 interface ports
    axi4_stream_if axi4_req,
    axi4_stream_if axi4_rsp,

    //Register File interface
    cag_rgm_rfs_if rfs_hmc
);

//----------------------------- Wiring openHMC controller
wire [DWIDTH-1:0]       to_serializers;
wire [DWIDTH-1:0]       from_deserializers;
wire [NUM_LANES-1:0]    bit_slip;
wire [NUM_LANES-1:0]    phy_lane_polarity;
bit 					phy_rx_ready;
bit                   P_RST_N;
//If transceiver models are used, clk_hmc should be sourced from the transceiver outclock and res_n hmc can be set independently
wire clk_hmc            = clk_user;       
wire res_n_hmc          = res_n;  

// Wire the HMC BFM model
wire            LxRXPS; // HMC input
wire            LxTXPS; // HMC output
wire            FERR_N; // HMC output
wire            LxTXPS_pullup;
assign          LxTXPS_pullup = (LxTXPS === 1'bz) ? 1'b1 : LxTXPS;
wire            FERR_N_pullup;
assign          FERR_N_pullup = (FERR_N === 1'bz) ? 1'b1 : FERR_N;

//----------------------------- Signal Routing from SerDes to HMC
wire [NUM_LANES-1:0] serial_Rx;
wire [NUM_LANES-1:0] serial_Txp;

//----------------------------- Attach the Register File System interface
assign rfs_hmc_if.clk = clk_hmc;
assign rfs_hmc_if.res_n = res_n;

//Assign the AXI4 IF
assign axi4_req.ACLK        = (`OPENHMC_ASYNC_FIFOS==0) ? clk_hmc : clk_user;
assign axi4_rsp.ACLK        = (`OPENHMC_ASYNC_FIFOS==0) ? clk_hmc : clk_user;
assign axi4_req.ARESET_N    = (`OPENHMC_ASYNC_FIFOS==0) ? res_n_hmc : res_n;
assign axi4_rsp.ARESET_N    = (`OPENHMC_ASYNC_FIFOS==0) ? res_n_hmc : res_n;

//------------------------------ Attach the HMC Link interface
 assign hmc.REFCLKP = clk_hmc_refclk;
 assign hmc.REFCLKN = ~clk_hmc_refclk;
 assign FERR_N  = hmc.FERR_N;
 assign hmc.REFCLK_BOOT = 2'b00; // 00 -> 125 MHz, 01 -> 156.25 MHz, 10 -> 166.67 MHz
 assign hmc.P_RST_N = P_RST_N;
 assign LxTXPS = hmc.TXPS;
 assign hmc.RXPS = LxRXPS;
	
 assign hmc.RXP = NUM_LANES==8 ? {8'h0, serial_Txp[NUM_LANES-1:0]} : serial_Txp; // Controller Tx is Cube Rx
 assign hmc.RXN = ~hmc.RXP;//NUM_LANES==8 ? {8'h0, ~serial_Txp[NUM_LANES-1:0]} : ~serial_Txp; // Controller Tx is Cube Rx
 assign serial_Rx = hmc.TXP; // Controller Rx is Cube Tx

//----------------------------- Generate Clocks
bit clk_10G;
generate
    begin : clocking_gen
        initial clk_10G = 1'b1;
        always #0.05ns clk_10G = ~clk_10G;  
    end
endgenerate

//----------------------------- Behavioral SerDes
bit LxTXPS_synced;
bit res_n_synced;
genvar lane;
generate
    begin : serializers_gen

        for (lane=0; lane<NUM_LANES; lane++) begin : behavioral_gen
            serializer #(
                .DWIDTH(LANE_WIDTH)
            ) serializer_I (
                .clk(clk_hmc),
                .res_n(res_n),
                .fast_clk(clk_10G),
                .data_in(to_serializers[lane*LANE_WIDTH+LANE_WIDTH-1:lane*LANE_WIDTH]),
                .data_out(serial_Txp[lane])
            );
            deserializer #(
                .DWIDTH(LANE_WIDTH)
            ) deserializer_I (
                .clk(clk_hmc),
                .res_n(LxTXPS_synced && res_n),
                .fast_clk(clk_10G),
                .bit_slip(bit_slip[lane]),
                .lane_polarity(phy_lane_polarity[lane]),
                .data_in(serial_Rx[lane]),
                .data_out(from_deserializers[lane*LANE_WIDTH+LANE_WIDTH-1:lane*LANE_WIDTH])
            );
        end
    end
endgenerate

always @(LxTXPS) phy_rx_ready   <= #500ns LxTXPS;
always @(posedge clk_hmc) LxTXPS_synced <= LxTXPS;

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================
openhmc_top #(
    .LOG_FPW(LOG_FPW),
    .FPW(FPW),
    .LOG_NUM_LANES(LOG_NUM_LANES),
    //Configure the Functionality
    .LOG_MAX_RX_TOKENS(10),                //That is max 1023 Tokens
    .LOG_MAX_HMC_TOKENS(10),                //That is max 1023 Tokens
    .HMC_RX_AC_COUPLED(1),
    .CTRL_LANE_POLARITY(1),
    .CTRL_LANE_REVERSAL(1),
    .BITSLIP_SHIFT_RIGHT(1),
    .OPEN_RSP_MODE(`OPEN_RSP_MODE),
	.SYNC_AXI4_IF(`OPENHMC_ASYNC_FIFOS==0),
    // Debug Logic
    .DBG_RX_TOKEN_MON(1)    //Required by the test check sequence
 )
openhmc_instance
 (

    //----------------------------------
    //----SYSTEM INTERFACES
    //----------------------------------
    .clk_user(clk_user),
    .clk_hmc(clk_hmc),
    .res_n_user(res_n),
    .res_n_hmc(res_n),

    //----------------------------------
    //----Connect HMC Controller
    //----------------------------------
    //to TX
    .s_axis_tx_TVALID(axi4_req.TVALID),
    .s_axis_tx_TREADY(axi4_req.TREADY),
    .s_axis_tx_TDATA(axi4_req.TDATA),
    .s_axis_tx_TUSER(axi4_req.TUSER),
    //from RX
    .m_axis_rx_TVALID(axi4_rsp.TVALID),
    .m_axis_rx_TREADY(axi4_rsp.TREADY),
    .m_axis_rx_TDATA(axi4_rsp.TDATA),
    .m_axis_rx_TUSER(axi4_rsp.TUSER),

    //----------------------------------
    //----Connect Physical Link
    //----------------------------------
    .phy_data_tx_link2phy(to_serializers),
    .phy_data_rx_phy2link(from_deserializers),
    .phy_bit_slip(bit_slip),
    .phy_tx_ready(res_n),
    .phy_rx_ready(phy_rx_ready && LxTXPS),
    .phy_lane_polarity(phy_lane_polarity),
    .phy_init_cont_set(),

    //----------------------------------
    //----Connect HMC
    //----------------------------------
    .P_RST_N(P_RST_N),
    .LXRXPS(LxRXPS),
    .LXTXPS(LxTXPS_pullup),
    .FERR_N(FERR_N_pullup),

    //----------------------------------
    //----Connect RF
    //----------------------------------
    .rf_address(rfs_hmc.address),
    .rf_read_data(rfs_hmc.read_data),
    .rf_invalid_address(rfs_hmc.invalid_address),
    .rf_access_complete(rfs_hmc.access_done),
    .rf_read_en(rfs_hmc.ren),
    .rf_write_en(rfs_hmc.wen),
    .rf_write_data(rfs_hmc.write_data)

    );

endmodule : dut

`default_nettype wire

