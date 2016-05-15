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
 *  Module name: openhmc_top
 *
 *
 *
 *
 *  DESIGN CONTROL: Use the following defines if desired:
 *  `define XILINX
 *          Uses Xilinx DSP48 as counter in the Register File
 *  `define ASYNC_RES
 *          Define the active low reset to be asynchronous
 *  `define RESET_ALL
 *          Use Reset values for all registers
 */

`default_nettype none

module openhmc_top #(
    //Define width of the datapath
    parameter FPW                   = 4,        //Legal Values: 2,4,6,8
    parameter LOG_FPW               = 2,        //Legal Values: 1 for FPW=2 ,2 for FPW=4 ,3 for FPW=6/8
    parameter DWIDTH                = FPW*128,  //Leave untouched
    //Define HMC interface width
    parameter LOG_NUM_LANES         = 3,                //Set 3 for half-width, 4 for full-width
    parameter NUM_LANES             = 2**LOG_NUM_LANES, //Leave untouched
    parameter NUM_DATA_BYTES        = FPW*16,           //Leave untouched
    //Define width of the register file
    parameter HMC_RF_WWIDTH         = 64,   //Leave untouched    
    parameter HMC_RF_RWIDTH         = 64,   //Leave untouched
    parameter HMC_RF_AWIDTH         = 4,    //Leave untouched
    //Configure the Functionality
    parameter LOG_MAX_RX_TOKENS     = 8,    //Set the depth of the RX input buffer. Must be >= LOG(rf_rx_buffer_rtc) in the RF. Dont't care if OPEN_RSP_MODE=1
    parameter LOG_MAX_HMC_TOKENS    = 10,   //Set the depth of the HMC input buffer. Must be >= LOG of the corresponding field in the HMC internal register
    parameter HMC_RX_AC_COUPLED     = 1,    //Set to 0 to bypass the run length limiter, saves logic and 1 cycle delay
    parameter DETECT_LANE_POLARITY  = 1,    //Set to 0 if lane polarity is not applicable, saves logic
    parameter CTRL_LANE_POLARITY    = 1,    //Set to 0 if lane polarity is not applicable or performed by the transceivers, saves logic and 1 cycle delay
                                            //If set to 1: Only valid if DETECT_LANE_POLARITY==1, otherwise tied to zero
    parameter CTRL_LANE_REVERSAL    = 1,    //Set to 0 if lane reversal is not applicable or performed by the transceivers, saves logic
    parameter CTRL_SCRAMBLERS       = 1,    //Set to 0 to remove the option to disable (de-)scramblers for debugging, saves logic
    parameter OPEN_RSP_MODE         = 0,    //Set to 1 if running response open loop mode, bypasses the RX input buffer
    parameter RX_RELAX_INIT_TIMING  = 1,    //Per default, incoming TS1 sequences are only checked for the lane independent h'F0 sequence. Save resources and
                                            //eases timing closure. !Lane reversal is still detected
    parameter RX_BIT_SLIP_CNT_LOG   = 5,    //Define the number of cycles between bit slips. Refer to the transceiver user guide
                                            //Example: RX_BIT_SLIP_CNT_LOG=5 results in 2^5=32 cycles between two bit slips
    parameter SYNC_AXI4_IF          = 0,    //Set to 1 if AXI IF is synchronous to clk_hmc to use simple fifos
    parameter XIL_CNT_PIPELINED     = 1,    //If Xilinx counters are used, set to 1 to enabled output register pipelining
    //Set the direction of bitslip. Set to 1 if bitslip performs a shift right, otherwise set to 0 (see the corresponding transceiver user guide)
    parameter BITSLIP_SHIFT_RIGHT   = 1,    
    //Debug Params
    parameter DBG_RX_TOKEN_MON      = 1     //Set to 0 to remove the RX Link token monitor, saves logic
) (
    //----------------------------------
    //----SYSTEM INTERFACES
    //----------------------------------
    input  wire                         clk_user,   //Connect if SYNC_AXI4_IF==0
    input  wire                         clk_hmc,    //Connect!
    input  wire                         res_n_user, //Connect if SYNC_AXI4_IF==0
    input  wire                         res_n_hmc,  //Connect!

    //----------------------------------
    //----Connect AXI Ports
    //----------------------------------
    //From AXI to HMC Ctrl TX
    input  wire                         s_axis_tx_TVALID,
    output wire                         s_axis_tx_TREADY,
    input  wire [DWIDTH-1:0]            s_axis_tx_TDATA,
    input  wire [NUM_DATA_BYTES-1:0]    s_axis_tx_TUSER,
    //From HMC Ctrl RX to AXI
    output wire                         m_axis_rx_TVALID,
    input  wire                         m_axis_rx_TREADY,
    output wire [DWIDTH-1:0]            m_axis_rx_TDATA,
    output wire [NUM_DATA_BYTES-1:0]    m_axis_rx_TUSER,

    //----------------------------------
    //----Connect Transceiver
    //----------------------------------
    output wire  [DWIDTH-1:0]           phy_data_tx_link2phy,//Connect!
    input  wire  [DWIDTH-1:0]           phy_data_rx_phy2link,//Connect!
    output wire  [NUM_LANES-1:0]        phy_bit_slip,       //Must be connected if DETECT_LANE_POLARITY==1 AND CTRL_LANE_POLARITY=0
    output wire  [NUM_LANES-1:0]        phy_lane_polarity,  //All 0 if CTRL_LANE_POLARITY=1
    input  wire                         phy_tx_ready,       //Optional information to RF
    input  wire                         phy_rx_ready,       //Release RX descrambler reset when PHY ready
    output wire                         phy_init_cont_set,  //Can be used to release transceiver reset if used

    //----------------------------------
    //----Connect HMC
    //----------------------------------
    output wire                         P_RST_N,
    output wire                         LXRXPS,
    input  wire                         LXTXPS,
    input  wire                         FERR_N,

    //----------------------------------
    //----Connect RF
    //----------------------------------
    input  wire  [HMC_RF_AWIDTH-1:0]    rf_address,
    output wire  [HMC_RF_RWIDTH-1:0]    rf_read_data,
    output wire                         rf_invalid_address,
    output wire                         rf_access_complete,
    input  wire                         rf_read_en,
    input  wire                         rf_write_en,
    input  wire  [HMC_RF_WWIDTH-1:0]    rf_write_data

    );

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

localparam MAX_RTC_RET_LOG   =   (FPW == 2) ? 6 :
                                 (FPW == 4) ? 7 :
                                 8;

`ifdef XILINX
    localparam RF_COUNTER_SIZE          = 48;
`else
    localparam RF_COUNTER_SIZE          = 64;
`endif                                 

// ----Assign AXI interface wires
wire [4*FPW-1:0]            m_axis_rx_TUSER_temp;
assign                      m_axis_rx_TUSER = {{NUM_DATA_BYTES-(4*FPW){1'b0}}, m_axis_rx_TUSER_temp};

wire   s_axis_tx_TREADY_n;
assign s_axis_tx_TREADY =   ~s_axis_tx_TREADY_n;
wire   m_axis_rx_TVALID_n;
assign m_axis_rx_TVALID =   ~m_axis_rx_TVALID_n;

// ----TX FIFO Wires
wire    [DWIDTH-1:0]        tx_d_in_data;
wire                        tx_shift_out;
wire                        tx_empty;
wire                        tx_a_empty;
wire    [3*FPW-1:0]         tx_d_in_ctrl;

// ----RX FIFO Wires
wire    [DWIDTH-1:0]        rx_d_in_data;
wire                        rx_shift_in;
wire                        rx_a_full;
wire    [4*FPW-1:0]         rx_d_in_ctrl;

// ----RX LINK TO TX LINK
wire                        rx2tx_link_retry;
wire                        rx2tx_error_abort_mode;
wire                        rx2tx_error_abort_mode_cleared;
wire    [7:0]               rx2tx_hmc_frp;
wire    [7:0]               rx2tx_rrp;
wire    [MAX_RTC_RET_LOG-1:0]rx2tx_returned_tokens;
wire    [LOG_FPW:0]         rx2tx_hmc_tokens_to_return;
wire    [LOG_FPW:0]         rx2tx_hmc_poisoned_tokens_to_return;

// ----Register File
//Counter
wire                        rf_cnt_retry;
wire                        rf_run_length_bit_flip;
wire                        rf_error_abort_not_cleared;
wire  [RF_COUNTER_SIZE-1:0] rf_cnt_poisoned;
wire  [RF_COUNTER_SIZE-1:0] rf_cnt_p;
wire  [RF_COUNTER_SIZE-1:0] rf_cnt_np;
wire  [RF_COUNTER_SIZE-1:0] rf_cnt_r;
wire  [RF_COUNTER_SIZE-1:0] rf_cnt_rsp_rcvd;
//Status
wire                        rf_link_up;
wire [2:0]                  rf_rx_init_status;
wire [1:0]                  rf_tx_init_status;
wire [LOG_MAX_HMC_TOKENS-1:0]rf_hmc_tokens_av;
wire [LOG_MAX_RX_TOKENS-1:0]rf_rx_tokens_av;
//Init Status
wire                        rf_all_descramblers_aligned;
wire [NUM_LANES-1:0]        rf_descrambler_aligned;
wire [NUM_LANES-1:0]        rf_descrambler_part_aligned;
//Control
wire                        rf_hmc_init_cont_set;
wire                        rf_set_hmc_sleep;
wire                        rf_warm_reset;
wire                        rf_scrambler_disable;
wire [NUM_LANES-1:0]        rf_lane_polarity;
wire [NUM_LANES-1:0]        rf_descramblers_locked;
wire [LOG_MAX_RX_TOKENS-1:0]rf_rx_buffer_rtc;
wire                        rf_lane_reversal_detected;
wire [4:0]                  rf_irtry_received_threshold;
wire [4:0]                  rf_irtry_to_send;
wire                        rf_run_length_enable;

assign phy_init_cont_set = rf_hmc_init_cont_set;

//Generate
wire                    rf_scrambler_disable_temp;
wire [LOG_MAX_RX_TOKENS-1:0]  rf_rx_buffer_rtc_temp;
generate
    if(CTRL_SCRAMBLERS==1) begin : ctrl_scramblers
        assign rf_scrambler_disable = rf_scrambler_disable_temp;
    end else begin : remove_scrambler_disable_bit
        assign rf_scrambler_disable = 1'b0;
    end
    if(OPEN_RSP_MODE==1) begin : remove_rx_tokens_rsp_open_loop_mode
        assign rf_rx_buffer_rtc = {LOG_MAX_RX_TOKENS{1'b0}};
    end else begin : regular_mode_use_rx_tokens
        assign rf_rx_buffer_rtc = rf_rx_buffer_rtc_temp;
    end
endgenerate

// ----Assign PHY wires
assign phy_lane_polarity = (CTRL_LANE_POLARITY==1) ? {NUM_LANES{1'b0}} : rf_lane_polarity;

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================
//----------------------------------------------------------------------
//-----TX-----TX-----TX-----TX-----TX-----TX-----TX-----TX-----TX-----TX
//----------------------------------------------------------------------
generate
    if(SYNC_AXI4_IF==0) begin : async_axi4_tx_fifo
        openhmc_async_fifo #(
            .DWIDTH(DWIDTH+(FPW*3)),
            .ENTRIES(16)
        ) fifo_tx_data (
            //System
            .si_clk(clk_user),
            .so_clk(clk_hmc),
            .si_res_n(res_n_user),
            .so_res_n(res_n_hmc),

            //From AXI-4 TX IF
            .d_in({s_axis_tx_TUSER[(FPW*3)-1:0],s_axis_tx_TDATA}),
            .shift_in(s_axis_tx_TVALID && s_axis_tx_TREADY),
            .full(s_axis_tx_TREADY_n),
            .almost_full(),

            //To TX Link Logic
            .d_out({tx_d_in_ctrl,tx_d_in_data}),
            .shift_out(tx_shift_out),
            .empty(tx_empty),
            .almost_empty(tx_a_empty)
        );
    end else begin : synchronous_axi4_tx_fifo
    `ifdef XILINX
        openhmc_sync_fifo_xilinx #(
            .DWIDTH(DWIDTH+(FPW*3))
        ) fifo_tx_data_sync_xilinx(
            //System
            .clk(clk_hmc),
            .res_n(res_n_hmc),

            //To RX LINK Logic
            .d_in({s_axis_tx_TUSER[(FPW*3)-1:0],s_axis_tx_TDATA}),
            .shift_in(s_axis_tx_TVALID && s_axis_tx_TREADY),
            .full(s_axis_tx_TREADY_n),
            .almost_full(),

            //AXI-4 RX IF
            .d_out({tx_d_in_ctrl,tx_d_in_data}),
            .shift_out(tx_shift_out),
            .empty(tx_empty),
            .almost_empty(tx_a_empty)
        );        
    `else        
        openhmc_sync_fifo_reg_based #(
            .DWIDTH(DWIDTH+(FPW*3)),
            .ENTRIES(4)
        ) fifo_tx_data_sync(
            //System
            .clk(clk_hmc),
            .res_n(res_n_hmc),

            //To RX LINK Logic
            .d_in({s_axis_tx_TUSER[(FPW*3)-1:0],s_axis_tx_TDATA}),
            .shift_in(s_axis_tx_TVALID && s_axis_tx_TREADY),
            .full(s_axis_tx_TREADY_n),
            .almost_full(),

            //AXI-4 RX IF
            .d_out({tx_d_in_ctrl,tx_d_in_data}),
            .shift_out(tx_shift_out),
            .empty(tx_empty),
            .almost_empty(tx_a_empty)
        );
    `endif
    end
endgenerate


tx_link #(
    .LOG_FPW(LOG_FPW),
    .FPW(FPW),
    .NUM_LANES(NUM_LANES),
    .RF_COUNTER_SIZE(RF_COUNTER_SIZE),
    .HMC_RX_AC_COUPLED(HMC_RX_AC_COUPLED),
    .MAX_RTC_RET_LOG(MAX_RTC_RET_LOG),
    .LOG_MAX_RX_TOKENS(LOG_MAX_RX_TOKENS),
    .LOG_MAX_HMC_TOKENS(LOG_MAX_HMC_TOKENS),
    .XIL_CNT_PIPELINED(XIL_CNT_PIPELINED),
    //Debug
    .DBG_RX_TOKEN_MON(DBG_RX_TOKEN_MON),
    .OPEN_RSP_MODE(OPEN_RSP_MODE)
) tx_link_I(

    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    .clk(clk_hmc),
    .res_n(res_n_hmc),

    //----------------------------------
    //----TO HMC PHY
    //----------------------------------
    .phy_scrambled_data_out(phy_data_tx_link2phy),

    //----------------------------------
    //----HMC IF
    //----------------------------------
    .LXRXPS(LXRXPS),
    .LXTXPS(LXTXPS),

    //----------------------------------
    //----FROM HMC_TX_HTAX_LOGIC
    //----------------------------------
    .d_in_data(tx_d_in_data),
    .d_in_flit_is_valid(tx_d_in_ctrl[FPW-1:0]),
    .d_in_flit_is_hdr(tx_d_in_ctrl[(2*FPW)-1:1*FPW]),
    .d_in_flit_is_tail(tx_d_in_ctrl[(3*FPW)-1:(2*FPW)]),
    .d_in_empty(tx_empty),
    .d_in_a_empty(tx_a_empty),
    .d_in_shift_out(tx_shift_out),

    //----------------------------------
    //----RX Block
    //----------------------------------
    .rx_force_tx_retry(rx2tx_link_retry),
    .rx_error_abort_mode(rx2tx_error_abort_mode),
    .rx_error_abort_mode_cleared(rx2tx_error_abort_mode_cleared),
    .rx_hmc_frp(rx2tx_hmc_frp),
    .rx_rrp(rx2tx_rrp),
    .rx_returned_tokens(rx2tx_returned_tokens),
    .rx_hmc_tokens_to_return(rx2tx_hmc_tokens_to_return),
    .rx_hmc_poisoned_tokens_to_return(rx2tx_hmc_poisoned_tokens_to_return),

    //----------------------------------
    //----RF
    //----------------------------------
    //Monitoring    1-cycle set to increment
    .rf_cnt_retry(rf_cnt_retry),
    .rf_sent_p(rf_cnt_p),
    .rf_sent_np(rf_cnt_np),
    .rf_sent_r(rf_cnt_r),
    .rf_run_length_bit_flip(rf_run_length_bit_flip),
    .rf_error_abort_not_cleared(rf_error_abort_not_cleared),
    //Status
    .rf_hmc_received_init_null(rf_rx_init_status==3'b010),
    .rf_link_is_up(rf_link_up),
    .rf_descramblers_aligned(rf_all_descramblers_aligned),
    .rf_tx_init_status(rf_tx_init_status),
    .rf_hmc_tokens_av(rf_hmc_tokens_av),
    .rf_rx_tokens_av(rf_rx_tokens_av),
    //Control
    .rf_hmc_sleep_requested(rf_set_hmc_sleep),
    .rf_warm_reset(rf_warm_reset),
    .rf_scrambler_disable(rf_scrambler_disable),
    .rf_rx_buffer_rtc(rf_rx_buffer_rtc),
    .rf_irtry_to_send(rf_irtry_to_send),
    .rf_run_length_enable(rf_run_length_enable)

);

//----------------------------------------------------------------------
//-----RX-----RX-----RX-----RX-----RX-----RX-----RX-----RX-----RX-----RX
//----------------------------------------------------------------------
rx_link #(
    .LOG_FPW(LOG_FPW),
    .FPW(FPW),
    .LOG_NUM_LANES(LOG_NUM_LANES),
    .RF_COUNTER_SIZE(RF_COUNTER_SIZE),
    //Configure the functionality
    .XIL_CNT_PIPELINED(XIL_CNT_PIPELINED),
    .LOG_MAX_RX_TOKENS(LOG_MAX_RX_TOKENS),
    .MAX_RTC_RET_LOG(MAX_RTC_RET_LOG),
    .RX_BIT_SLIP_CNT_LOG(RX_BIT_SLIP_CNT_LOG),
    .CTRL_LANE_POLARITY(CTRL_LANE_POLARITY),
    .DETECT_LANE_POLARITY(DETECT_LANE_POLARITY),
    .CTRL_LANE_REVERSAL(CTRL_LANE_REVERSAL),
    .BITSLIP_SHIFT_RIGHT(BITSLIP_SHIFT_RIGHT),
    .OPEN_RSP_MODE(OPEN_RSP_MODE),
    .RX_RELAX_INIT_TIMING(RX_RELAX_INIT_TIMING)
) rx_link_I (

    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    .clk(clk_hmc),
    .res_n(res_n_hmc),

    //----------------------------------
    //----TO HMC PHY
    //----------------------------------
    .phy_scrambled_data_in(phy_data_rx_phy2link),
    .phy_bit_slip(phy_bit_slip),
    .run_rx(phy_rx_ready),

    //----------------------------------
    //----FROM TO RX HTAX FIFO
    //----------------------------------
    .d_out_fifo_data(rx_d_in_data),
    .d_out_fifo_a_full(rx_a_full),
    .d_out_fifo_shift_in(rx_shift_in),
    .d_out_fifo_ctrl(rx_d_in_ctrl),

    //----------------------------------
    //----TO TX Block
    //----------------------------------
    .tx_link_retry(rx2tx_link_retry),
    .tx_error_abort_mode(rx2tx_error_abort_mode),
    .tx_error_abort_mode_cleared(rx2tx_error_abort_mode_cleared),
    .tx_hmc_frp(rx2tx_hmc_frp),
    .tx_rrp(rx2tx_rrp),
    .tx_returned_tokens(rx2tx_returned_tokens),
    .tx_hmc_tokens_to_return(rx2tx_hmc_tokens_to_return),
    .tx_hmc_poisoned_tokens_to_return(rx2tx_hmc_poisoned_tokens_to_return),

    //----------------------------------
    //----RF
    //----------------------------------
    //Monitoring    1-cycle set to increment
    .rf_cnt_poisoned(rf_cnt_poisoned),
    .rf_cnt_rsp(rf_cnt_rsp_rcvd),
    //Status
    .rf_link_up(rf_link_up),
    .rf_rx_init_status(rf_rx_init_status),
    .rf_hmc_sleep(~LXTXPS),
    //Init Status
    .rf_all_descramblers_aligned(rf_all_descramblers_aligned),
    .rf_descrambler_aligned(rf_descrambler_aligned),
    .rf_descrambler_part_aligned(rf_descrambler_part_aligned),
    .rf_descramblers_locked(rf_descramblers_locked),
    //Control
    .rf_lane_polarity(rf_lane_polarity),
    .rf_scrambler_disable(rf_scrambler_disable),
    .rf_lane_reversal_detected(rf_lane_reversal_detected),
    .rf_irtry_received_threshold(rf_irtry_received_threshold)
);

generate
    if(SYNC_AXI4_IF==0) begin : async_axi4_rx_fifo
        openhmc_async_fifo #(
            .DWIDTH(DWIDTH+(FPW*4)),
            .ENTRIES(16)
        ) fifo_rx_data(
            //System
            .si_clk(clk_hmc),
            .so_clk(clk_user),
            .si_res_n(res_n_hmc),
            .so_res_n(res_n_user),

            //To RX LINK Logic
            .d_in({rx_d_in_ctrl,rx_d_in_data}),
            .shift_in(rx_shift_in),
            .full(),
            .almost_full(rx_a_full),

            //AXI-4 RX IF
            .d_out({m_axis_rx_TUSER_temp,m_axis_rx_TDATA}),
            .shift_out(m_axis_rx_TVALID && m_axis_rx_TREADY),
            .empty(m_axis_rx_TVALID_n),
            .almost_empty()

        );
    end else begin : synchronous_axi4_rx_fifo
    `ifdef XILINX
        openhmc_sync_fifo_xilinx #(
            .DWIDTH(DWIDTH+(FPW*4))
        ) fifo_rx_data_sync_xilinx(
            //System
            .clk(clk_hmc),
            .res_n(res_n_hmc),

            //To RX LINK Logic
            .d_in({rx_d_in_ctrl,rx_d_in_data}),
            .shift_in(rx_shift_in),
            .full(),
            .almost_full(rx_a_full),

            //AXI-4 RX IF
            .d_out({m_axis_rx_TUSER_temp,m_axis_rx_TDATA}),
            .shift_out(m_axis_rx_TVALID && m_axis_rx_TREADY),
            .empty(m_axis_rx_TVALID_n),
            .almost_empty()
        );        
    `else 
        openhmc_sync_fifo_reg_based #(
            .DWIDTH(DWIDTH+(FPW*4)),
            .ENTRIES(4)
        ) fifo_rx_data_sync(
            //System
            .clk(clk_hmc),
            .res_n(res_n_hmc),

            //To RX LINK Logic
            .d_in({rx_d_in_ctrl,rx_d_in_data}),
            .shift_in(rx_shift_in),
            .full(),
            .almost_full(rx_a_full),

            //AXI-4 RX IF
            .d_out({m_axis_rx_TUSER_temp,m_axis_rx_TDATA}),
            .shift_out(m_axis_rx_TVALID && m_axis_rx_TREADY),
            .empty(m_axis_rx_TVALID_n),
            .almost_empty()
        );
    `endif
    end
endgenerate

//----------------------------------------------------------------------
//---Register File---Register File---Register File---Register File---Reg
//----------------------------------------------------------------------
    openhmc_rf #(
        .NUM_LANES(NUM_LANES),
        .XIL_CNT_PIPELINED(XIL_CNT_PIPELINED),
        .LOG_MAX_RX_TOKENS(LOG_MAX_RX_TOKENS),
        .LOG_MAX_HMC_TOKENS(LOG_MAX_HMC_TOKENS),
        .RF_COUNTER_SIZE(RF_COUNTER_SIZE),
        .HMC_RF_WWIDTH(HMC_RF_WWIDTH),
        .HMC_RF_AWIDTH(HMC_RF_AWIDTH),
        .HMC_RF_RWIDTH(HMC_RF_RWIDTH)
    ) openhmc_rf_I (
        //system IF
        .res_n(res_n_hmc),
        .clk(clk_hmc),

        //rf access
        .address(rf_address),
        .read_data(rf_read_data),
        .invalid_address(rf_invalid_address),
        .access_complete(rf_access_complete),
        .read_en(rf_read_en),
        .write_en(rf_write_en),
        .write_data(rf_write_data),

        //status registers
        .status_general_link_up_next(rf_link_up),
        .status_general_link_training_next(~rf_link_up),
        .status_general_sleep_mode_next(~LXTXPS),
        .status_general_FERR_N_next(FERR_N),
        .status_general_phy_tx_ready_next(phy_tx_ready),
        .status_general_phy_rx_ready_next(phy_rx_ready),
        .status_general_lanes_reversed_next(rf_lane_reversal_detected),
        .status_general_hmc_tokens_remaining_next(rf_hmc_tokens_av),
        .status_general_rx_tokens_remaining_next(rf_rx_tokens_av),
        .status_general_lane_polarity_reversed_next(rf_lane_polarity),

        //init status
        .status_init_lane_descramblers_locked_next(rf_descramblers_locked),
        .status_init_descrambler_part_aligned_next(rf_descrambler_part_aligned),
        .status_init_descrambler_aligned_next(rf_descrambler_aligned),
        .status_init_all_descramblers_aligned_next(rf_all_descramblers_aligned),
        .status_init_rx_init_state_next(rf_rx_init_status),
        .status_init_tx_init_state_next(rf_tx_init_status),

        //counters
        .sent_np_cnt_next(rf_cnt_np),
        .sent_p_cnt_next(rf_cnt_p),
        .sent_r_cnt_next(rf_cnt_r),
        .poisoned_packets_cnt_next(rf_cnt_poisoned),
        .rcvd_rsp_cnt_next(rf_cnt_rsp_rcvd),

        //Single bit counter
        .tx_link_retries_count_countup(rf_cnt_retry),
        .errors_on_rx_count_countup(rx2tx_error_abort_mode_cleared),
        .run_length_bit_flip_count_countup(rf_run_length_bit_flip),
        .error_abort_not_cleared_count_countup(rf_error_abort_not_cleared),

        //control
        .control_p_rst_n(P_RST_N),
        .control_hmc_init_cont_set(rf_hmc_init_cont_set),
        .control_set_hmc_sleep(rf_set_hmc_sleep),
        .control_warm_reset(rf_warm_reset),
        .control_scrambler_disable(rf_scrambler_disable_temp),
        .control_run_length_enable(rf_run_length_enable),
        .control_rx_token_count(rf_rx_buffer_rtc_temp),
        .control_irtry_received_threshold(rf_irtry_received_threshold),
        .control_irtry_to_send(rf_irtry_to_send)
    );

endmodule

`default_nettype wire