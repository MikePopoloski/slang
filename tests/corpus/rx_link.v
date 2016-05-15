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
 *  Module name: rx_link
 *
 */

`default_nettype none

module rx_link #(
    parameter LOG_FPW              = 2,
    parameter FPW                  = 4,
    parameter DWIDTH               = FPW*128,
    parameter LOG_NUM_LANES        = 3,
    parameter NUM_LANES            = 2**LOG_NUM_LANES,
    parameter HMC_PTR_SIZE         = 8,
    parameter RF_COUNTER_SIZE      = 64,
    //Set Token Related
    parameter LOG_MAX_RX_TOKENS    = 8,
    parameter MAX_RTC_RET_LOG      = 8,
    //Control
    parameter XIL_CNT_PIPELINED    = 0,
    parameter CTRL_LANE_POLARITY   = 1,
    parameter RX_RELAX_INIT_TIMING = 1,
    parameter RX_BIT_SLIP_CNT_LOG  = 5,
    parameter DETECT_LANE_POLARITY = 1,
    parameter CTRL_LANE_REVERSAL   = 1,
    parameter BITSLIP_SHIFT_RIGHT  = 1,
    parameter OPEN_RSP_MODE        = 0
) (

    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    input   wire                        clk,
    input   wire                        res_n,
    input   wire                        run_rx,

    //----------------------------------
    //----TO HMC PHY
    //----------------------------------
    input   wire  [DWIDTH-1:0]          phy_scrambled_data_in,
    output  reg   [NUM_LANES-1:0]       phy_bit_slip,

    //----------------------------------
    //----TO RX HTAX FIFO
    //----------------------------------
    output  wire   [DWIDTH-1:0]         d_out_fifo_data,
    input   wire                        d_out_fifo_a_full,
    output  wire                        d_out_fifo_shift_in,
    output  wire   [4*FPW-1:0]          d_out_fifo_ctrl,

    //----------------------------------
    //----TO TX Block
    //----------------------------------
    output  reg                         tx_link_retry,
    output  reg                         tx_error_abort_mode,
    output  reg                         tx_error_abort_mode_cleared,
    output  reg   [7:0]                 tx_hmc_frp,
    output  reg   [7:0]                 tx_rrp,
    output  reg   [MAX_RTC_RET_LOG-1:0] tx_returned_tokens,
    output  wire  [LOG_FPW:0]           tx_hmc_tokens_to_return,
    output  wire  [LOG_FPW:0]           tx_hmc_poisoned_tokens_to_return,

    //----------------------------------
    //----RF
    //----------------------------------
    //Monitoring    1-cycle set to increment
    output  wire  [RF_COUNTER_SIZE-1:0] rf_cnt_poisoned,
    output  wire  [RF_COUNTER_SIZE-1:0] rf_cnt_rsp,
    //Status
    output  reg                         rf_link_up,
    output  reg   [2:0]                 rf_rx_init_status,
    input   wire                        rf_hmc_sleep,
    //Init Status
    output  wire  [NUM_LANES-1:0]       rf_descrambler_part_aligned,
    output  wire  [NUM_LANES-1:0]       rf_descrambler_aligned,
    output  wire                        rf_all_descramblers_aligned,
    //Control
    output  wire  [NUM_LANES-1:0]       rf_lane_polarity,           
    input   wire                        rf_scrambler_disable,
    output  wire                        rf_lane_reversal_detected,
    output  reg   [NUM_LANES-1:0]       rf_descramblers_locked,
    input   wire  [4:0]                 rf_irtry_received_threshold

);
`include "hmc_field_functions.h"

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

//------------------------------------------------------------------------------------Some general things
//Link state -- Most likely will be encoded as one-hot FSM
localparam              HMC_DOWN            = 3'b000;
localparam              HMC_WAIT_FOR_NULL   = 3'b001;
localparam              HMC_NULL            = 3'b010;
localparam              HMC_TS1_PART_ALIGN  = 3'b011;
localparam              HMC_TS1_FIND_REF    = 3'b100;
localparam              HMC_TS1_ALIGN       = 3'b101;
localparam              HMC_NULL_NEXT       = 3'b110;
localparam              HMC_UP              = 3'b111;

//Commands
localparam              CMD_IRTRY           = 6'b000011;
localparam              CMD_RSP_ERROR       = 6'b111110;

//Other helpful defines
localparam              WIDTH_PER_LANE          = (DWIDTH/NUM_LANES);

//16 bits is a ts1, so the init seq number is incremented according to the lane size
localparam              INIT_SEQ_INC_PER_CYCLE  = WIDTH_PER_LANE/16;

//MISC
integer i_f;    //counts to FPW
integer i_l;    //counts to NUM_LANES
integer i_c;    //counts to CYCLES_TO_COMPLETE_FULL_PACKET

genvar f;   //Counts to FPW
genvar n;   //Counts to NUM_LANES
genvar w;   //Counts to WIDTH_PER_LANE

//------------------------------------------------------------------------------------DESCRAMBLER AND DATA ORDERING
reg [NUM_LANES-1:0]     init_descrambler_part_aligned;
reg [NUM_LANES-1:0]     init_descrambler_aligned;
assign                  rf_descrambler_part_aligned = init_descrambler_part_aligned;
assign                  rf_descrambler_aligned      = init_descrambler_aligned;

//DATA and REORDERING
wire [128-1:0]              init_d_in_flit              [FPW-1:0];
wire [WIDTH_PER_LANE-1:0]   descrambled_data_per_lane   [NUM_LANES-1:0];
reg  [WIDTH_PER_LANE-1:0]   descrambled_data_per_lane_dly   [NUM_LANES-1:0];
wire [DWIDTH-1:0]           d_in;
wire [DWIDTH-1:0]           d_in_dly;
wire [128-1:0]              d_in_flit                   [FPW-1:0];

//Valid FLIT sources. A FLIT is valid when it is not NULL
wire [FPW-1:0]              valid_flit_src;         //bit0 = flit0, ...
wire [FPW-1:0]              init_valid_flit_src;    //bit0 = flit0, ...

generate

    //-- Apply lane reversal if detected
    for(n = 0; n < NUM_LANES; n = n + 1) begin : apply_lane_reversal
        for(w = 0; w < WIDTH_PER_LANE; w = w + 1) begin
            if(CTRL_LANE_REVERSAL==1)begin
                assign d_in[w*NUM_LANES+n]      = rf_lane_reversal_detected ? descrambled_data_per_lane[NUM_LANES-1-n][w] : descrambled_data_per_lane[n][w];
                assign d_in_dly[w*NUM_LANES+n]  = rf_lane_reversal_detected ? descrambled_data_per_lane_dly[NUM_LANES-1-n][w] : descrambled_data_per_lane_dly[n][w];
            end else begin
                assign d_in[w*NUM_LANES+n]      = descrambled_data_per_lane[n][w];
                assign d_in_dly[w*NUM_LANES+n]  = descrambled_data_per_lane_dly[n][w];
            end
        end
    end


    for(f = 0; f < FPW; f = f + 1) begin : reorder_input_data
        //-- Reorder the descrambled data to FLITs
        assign d_in_flit[f]       = d_in[128-1+(f*128):f*128];
        assign init_d_in_flit[f]  = d_in_dly[128-1+(f*128):f*128];
        //-- Generate valid flit positions
        assign valid_flit_src[f]        = |d_in_flit[f][5:0];
        assign init_valid_flit_src[f]   = |init_d_in_flit[f];
    end

endgenerate


//------------------------------------------------------------------------------------INIT
localparam                  LINK_DOWN   = 1'b0;
localparam                  LINK_UP     = 1'b1;

reg [NUM_LANES-1:0]         init_bit_slip;
reg [NUM_LANES-1:0]         init_bit_slip_part;
reg [RX_BIT_SLIP_CNT_LOG-1:0]init_bit_slip_cnt;
wire[NUM_LANES-1:0]         init_descrambler_locked;           //locked from the descrambler
reg [3:0]                   init_tmp_seq;

assign                      rf_all_descramblers_aligned = &init_descrambler_aligned;

//--------------TS1 recognition
localparam                  TS1_INDEPENDENT_PORTION = {4'hF,4'h0};
localparam                  TS1_LANE0_PORTION       = 4'h3;         //Not used if RX_RELAX_INIT_TIMING==1
localparam                  TS1_LANEX_PORTION       = 4'h5;         //Not used if RX_RELAX_INIT_TIMING==1
localparam                  TS1_LANE7OR15_PORTION   = 4'hc;

localparam                  TS1_SEQS_PER_CYCLE_AND_LANE = DWIDTH/NUM_LANES/16;

wire    [NUM_LANES-1:0]                  init_lane_has_correct_ts1;
wire    [TS1_SEQS_PER_CYCLE_AND_LANE-1:0]init_lane_has_correct_ts1_vec   [NUM_LANES-1:0];

genvar t;
generate
    //Make sure that the lanes have valid ts1 sequences throughout the entire data stream
    for(n=0;n<NUM_LANES;n=n+1) begin : lane_has_correct_ts1_gen
        assign init_lane_has_correct_ts1[n] = &init_lane_has_correct_ts1_vec[n];
    end

    for(t=0;t<TS1_SEQS_PER_CYCLE_AND_LANE;t=t+1) begin : ts1_recognition_gen
        if(RX_RELAX_INIT_TIMING==1) begin
            for(n=0;n<NUM_LANES;n=n+1) begin 
                assign init_lane_has_correct_ts1_vec[n][t] = (descrambled_data_per_lane[n][(t*16)+8+:8] == {TS1_INDEPENDENT_PORTION});
            end            
        end else begin
            for(n=1;n<NUM_LANES-1;n=n+1) begin 
                assign init_lane_has_correct_ts1_vec[n][t] = (descrambled_data_per_lane[n][(t*16)+4+:12] == {TS1_INDEPENDENT_PORTION,TS1_LANEX_PORTION});
            end
            assign init_lane_has_correct_ts1_vec[0][t] = (descrambled_data_per_lane[0][(t*16)+4+:12] == {TS1_INDEPENDENT_PORTION,TS1_LANE0_PORTION})||
                (CTRL_LANE_REVERSAL==1 ? descrambled_data_per_lane[0][(t*16)+4+:12] == {TS1_INDEPENDENT_PORTION,TS1_LANE7OR15_PORTION} : 0);
            assign init_lane_has_correct_ts1_vec[NUM_LANES-1][t] = (descrambled_data_per_lane[NUM_LANES-1][(t*16)+4+:12] == {TS1_INDEPENDENT_PORTION,TS1_LANE7OR15_PORTION})||
                (CTRL_LANE_REVERSAL==1 ? descrambled_data_per_lane[NUM_LANES-1][(t*16)+4+:12] == {TS1_INDEPENDENT_PORTION,TS1_LANE0_PORTION} : 0);                                                                     
        end
    end
endgenerate

//--------------Align the lanes, scan for the ts1 seq
wire [LOG_NUM_LANES-1:0] init_lane_cnt;
assign                   init_lane_cnt = init_bit_slip_cnt[LOG_NUM_LANES-1:0];
wire [3:0]               init_seq_diff;

//If one of the descramblers is already partially aligned search for other lanes with their ts1 sequence number close this lane. 
assign                   init_seq_diff = (BITSLIP_SHIFT_RIGHT==1 ? (descrambled_data_per_lane[init_lane_cnt][3:0] - init_tmp_seq) 
                                         : init_tmp_seq - descrambled_data_per_lane[init_lane_cnt][3:0]);

//------------------------------------------------------------------------------------Input Stage: Scan for Packets, Headers, Tails ...
reg  [FPW-1:0]          data2crc_hdr;
reg  [FPW-1:0]          data2crc_tail;
reg  [FPW-1:0]          data2crc_valid;
wire [(FPW*4)-1:0]      data2crc_lng;
reg  [3:0]              data2crc_lng_per_flit [FPW-1:0];
reg  [3:0]              data2crc_payload_remain;

reg  [FPW-1:0]          data2crc_hdr_comb;
reg  [FPW-1:0]          data2crc_tail_comb;
reg  [FPW-1:0]          data2crc_valid_comb;
reg  [3:0]              data2crc_lng_per_flit_comb [FPW-1:0];
reg  [3:0]              data2crc_payload_remain_comb;

generate
        for(f = 0; f < (FPW); f = f + 1) begin : reorder_crc_input
            assign data2crc_lng[(f*4)+:4] = data2crc_lng_per_flit[f];
        end
endgenerate

//------------------------------------------------------------------------------------CRC
wire [DWIDTH-1:0]       crc_d_out_data;
wire [128-1:0]          crc_d_out_flit              [FPW-1:0];
wire [FPW-1:0]          crc_d_out_flit_is_hdr;
wire [FPW-1:0]          crc_d_out_flit_is_tail;
wire [FPW-1:0]          crc_d_out_flit_is_valid;
wire [FPW-1:0]          crc_d_out_flit_is_error;
wire [FPW-1:0]          crc_d_out_flit_is_poisoned;
wire [FPW-1:0]          crc_d_out_flit_has_rtc;
wire [FPW-1:0]          crc_d_out_flit_is_flow;

generate
        for(f=0;f<FPW;f=f+1) begin : reorder_crc_output
            assign crc_d_out_flit[f] = crc_d_out_data[128-1+(f*128):f*128];
        end
endgenerate

//------------------------------------------------------------------------------------Start TX retry Stage
reg     [128-1:0]       flit_after_irtry_stage                   [FPW-1:0];
reg     [FPW-1:0]       flit_after_irtry_stage_is_hdr;
reg     [FPW-1:0]       flit_after_irtry_stage_is_tail;
reg     [FPW-1:0]       flit_after_irtry_stage_is_valid;
reg     [FPW-1:0]       flit_after_irtry_stage_is_error;
reg     [FPW-1:0]       flit_after_irtry_stage_is_poisoned;
reg     [FPW-1:0]       flit_after_irtry_stage_has_rtc;
reg     [FPW-1:0]       flit_after_irtry_stage_is_start_retry;
reg     [FPW-1:0]       flit_after_irtry_stage_is_clear_error;
reg     [FPW-1:0]       flit_after_irtry_stage_is_start_retry_comb;
reg     [FPW-1:0]       flit_after_irtry_stage_is_clear_error_comb;

//------------------------------------------------------------------------------------SeqStage and Seqnum
reg     [128-1:0]       flit_after_seq_check                   [FPW-1:0];
reg     [FPW-1:0]       flit_after_seq_check_is_hdr;
reg     [FPW-1:0]       flit_after_seq_check_is_tail;
reg     [FPW-1:0]       flit_after_seq_check_is_valid;
reg     [FPW-1:0]       flit_after_seq_check_is_error;
reg     [FPW-1:0]       flit_after_seq_check_is_error_comb;
reg     [FPW-1:0]       flit_after_seq_check_is_poisoned;
reg     [FPW-1:0]       flit_after_seq_check_has_rtc;
reg     [FPW-1:0]       flit_after_seq_check_is_start_retry;
reg     [FPW-1:0]       flit_after_seq_check_is_clear_error;

reg     [2:0]           next_seqnum;
reg     [2:0]           next_seqnum_comb; //can be reduced to [1:0] for 2FLIT config
reg     [2:0]           first_seq_after_error;

//------------------------------------------------------------------------------------IRTRY packet count stage
reg     [128-1:0]       flit_after_mask_stage                   [FPW-1:0];
reg     [FPW-1:0]       flit_after_mask_stage_is_hdr;
reg     [FPW-1:0]       flit_after_mask_stage_is_tail;
reg     [FPW-1:0]       flit_after_mask_stage_is_valid;
reg     [FPW-1:0]       flit_after_mask_stage_is_valid_mask_lsb;
reg     [FPW-1:0]       flit_after_mask_stage_is_valid_mask_msb;
reg     [FPW-1:0]       flit_after_mask_stage_is_error;
reg     [FPW-1:0]       flit_after_mask_stage_is_poisoned;
reg     [FPW-1:0]       flit_after_mask_stage_is_start_retry;
reg     [FPW-1:0]       flit_after_mask_stage_has_rtc;


//Assign FLITs to word, necessary for the invalidation stage pipeline
wire   [DWIDTH-1:0]            flit_after_mask_stage_word;
generate
        for(f = 0; f < (FPW); f = f + 1) begin : reorder_flits_to_word
            assign flit_after_mask_stage_word[(f*128)+128-1:(f*128)] = flit_after_mask_stage[f];
        end
endgenerate

//------------------------------------------------------------------------------------Invalidation Stage
//Assuming Max Pkt size = 9 FLITs
localparam CYCLES_TO_COMPLETE_FULL_PACKET   =   (FPW == 2) ? 5 :
                                                (FPW == 4) ? 3 :
                                                (FPW == 6) ? 3 :
                                                2;

//Regs to retrieve the pkt length, assign the length to correspoding tail. The packet will be invalidated then
reg     [3:0]        lng_per_tail      [FPW-1:0] ;
reg     [3:0]        lng_per_tail_comb [FPW-1:0] ;
reg     [3:0]        lng_temp;
reg     [3:0]        lng_comb;
//Signal that an error was detected. Invalidate all FLITs after
reg                  error;

reg     [DWIDTH-1:0]    flit_in_invalidation_data          [CYCLES_TO_COMPLETE_FULL_PACKET-1:0];
reg     [FPW-1:0]       flit_in_invalidation_is_hdr        [CYCLES_TO_COMPLETE_FULL_PACKET-1:0];
reg     [FPW-1:0]       flit_in_invalidation_is_tail       [CYCLES_TO_COMPLETE_FULL_PACKET-1:0];
reg     [FPW-1:0]       flit_in_invalidation_is_valid      [CYCLES_TO_COMPLETE_FULL_PACKET-1:0];
reg     [FPW-1:0]       flit_in_invalidation_mask_error;
reg     [FPW-1:0]       flit_in_invalidation_is_poisoned   [CYCLES_TO_COMPLETE_FULL_PACKET-1:0];
reg     [FPW-1:0]       flit_in_invalidation0_is_poisoned_comb;

//------------------------------------------------------------------------------------Checked FLITs
wire     [128-1:0]      checked_flit             [FPW-1:0];
wire     [FPW-1:0]      checked_flit_is_poisoned;
wire     [FPW-1:0]      checked_flit_is_valid;
wire     [FPW-1:0]      checked_flit_is_hdr;
wire     [FPW-1:0]      checked_flit_is_tail;

assign checked_flit_is_hdr         = flit_in_invalidation_is_hdr       [CYCLES_TO_COMPLETE_FULL_PACKET-1] & flit_in_invalidation_is_valid     [CYCLES_TO_COMPLETE_FULL_PACKET-1];
assign checked_flit_is_tail        = flit_in_invalidation_is_tail      [CYCLES_TO_COMPLETE_FULL_PACKET-1] & flit_in_invalidation_is_valid     [CYCLES_TO_COMPLETE_FULL_PACKET-1];
assign checked_flit_is_valid       = flit_in_invalidation_is_valid     [CYCLES_TO_COMPLETE_FULL_PACKET-1] ;
assign checked_flit_is_poisoned    = flit_in_invalidation_is_poisoned  [CYCLES_TO_COMPLETE_FULL_PACKET-1] & flit_in_invalidation_is_valid     [CYCLES_TO_COMPLETE_FULL_PACKET-1];

generate
        for(f = 0; f < (FPW); f = f + 1) begin : reorder_invalidation_word_back_to_flits
            assign checked_flit[f] = flit_in_invalidation_data[CYCLES_TO_COMPLETE_FULL_PACKET-1][128-1+(f*128):f*128];
        end
endgenerate

//------------------------------------------------------------------------------------Counter
reg [LOG_FPW:0]             rf_cnt_poisoned_comb;
reg [LOG_FPW:0]             rf_cnt_rsp_comb;

//------------------------------------------------------------------------------------Input Buffer
reg     [MAX_RTC_RET_LOG-1:0]rtc_sum_comb; //for 8 FLIT config, maximum 8*31 tokens will be returned per cycle

reg     [128-1:0]            input_buffer_d_in_flit    [FPW-1:0];
reg     [FPW-1:0]            input_buffer_is_valid;
reg     [FPW-1:0]            input_buffer_is_hdr;
reg     [FPW-1:0]            input_buffer_is_tail;
reg     [FPW-1:0]            input_buffer_is_error_rsp;
wire    [DWIDTH+(4*FPW)-1:0] input_buffer_d_in;
wire    [DWIDTH+(4*FPW)-1:0] input_buffer_d_out;
wire                         input_buffer_empty;
wire                         input_buffer_shift_in;
wire                         input_buffer_shift_out;
assign                       input_buffer_shift_out    =   ~(input_buffer_empty || d_out_fifo_a_full);

generate
        for(f = 0; f < (FPW); f = f + 1) begin : assign_flits_to_input_buffer_to_a_single_reg
            assign input_buffer_d_in[f*128+128-1:f*128] = input_buffer_d_in_flit[f];
            assign input_buffer_d_in[DWIDTH+f]          = input_buffer_is_valid[f];
            assign input_buffer_d_in[DWIDTH+f+FPW]      = input_buffer_is_hdr[f];
            assign input_buffer_d_in[DWIDTH+f+(2*FPW)]  = input_buffer_is_tail[f];
            assign input_buffer_d_in[DWIDTH+f+(3*FPW)]  = input_buffer_is_error_rsp[f];
        end
endgenerate

//------------------------------------------------------------------------------------LINK RETRY
reg  [4:0]     irtry_start_retry_cnt;
reg  [4:0]     irtry_clear_error_cnt;
reg  [4:0]     irtry_start_retry_cnt_comb;
reg  [4:0]     irtry_clear_error_cnt_comb;
reg            irtry_clear_trig;

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------ACTUAL LOGIC STARTS HERE--------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

//========================================================================================================================================
//------------------------------------------------------------------INIT
//========================================================================================================================================

generate
    if(CTRL_LANE_REVERSAL==1) begin : control_lane_reversal
        reg    init_lane_reversal_detected;
        assign rf_lane_reversal_detected = init_lane_reversal_detected;
        
        `ifdef ASYNC_RES
        always @(posedge clk or negedge res_n)  begin `else
        always @(posedge clk)  begin `endif
            if(!res_n) begin
                init_lane_reversal_detected   <= 1'b0;
            end else begin
                if(rf_rx_init_status==HMC_DOWN) begin
                    init_lane_reversal_detected   <= 1'b0;
                end
                if(rf_rx_init_status==HMC_TS1_ALIGN && rf_all_descramblers_aligned && (descrambled_data_per_lane[0][7:4] ==  TS1_LANE7OR15_PORTION)) begin
                    //lane reversal detected, reverse the input stream lane by lane
                    init_lane_reversal_detected   <= 1'b1;
                end
            end
        end
    end else begin
        assign rf_lane_reversal_detected = 1'b0;
    end

    if(DETECT_LANE_POLARITY==1) begin : detect_lane_reversal
        reg [NUM_LANES-1:0] init_lane_polarity;
        assign rf_lane_polarity = init_lane_polarity;
        `ifdef ASYNC_RES
        always @(posedge clk or negedge res_n)  begin `else
        always @(posedge clk)  begin `endif
            if(!res_n) begin
                init_lane_polarity        <= {NUM_LANES{1'b0}};
            end else begin
                if(rf_rx_init_status==HMC_DOWN) begin
                    init_lane_polarity    <= {NUM_LANES{1'b0}};
                end
                //Detect Lane polarity when HMC is sending first NULLs
                if(rf_rx_init_status==HMC_WAIT_FOR_NULL) begin
                    for(i_l = 0;i_l<NUM_LANES;i_l=i_l+1)begin
                        if(descrambled_data_per_lane[i_l] == {WIDTH_PER_LANE{1'b1}})begin
                            init_lane_polarity[i_l] <=  1'b1;
                        end
                    end
                end
            end
        end
    end else begin
        assign rf_lane_polarity = {NUM_LANES{1'b0}};
    end
endgenerate

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    for(i_l = 0;i_l<NUM_LANES;i_l=i_l+1)begin
        `ifdef RESET_ALL
            if(!res_n) descrambled_data_per_lane_dly[i_l] <= {WIDTH_PER_LANE{1'b0}};
            else
        `endif
        descrambled_data_per_lane_dly[i_l] <= descrambled_data_per_lane[i_l];
    end

if(!res_n) begin
    //----Misc
    init_descrambler_aligned        <= {NUM_LANES{1'b0}};
    init_descrambler_part_aligned   <= {NUM_LANES{1'b0}};
    phy_bit_slip                    <= {NUM_LANES{1'b0}};
    init_bit_slip                   <= {NUM_LANES{1'b0}};
    init_bit_slip_part              <= {NUM_LANES{1'b0}};
    init_bit_slip_cnt               <= {RX_BIT_SLIP_CNT_LOG{1'b0}};
    init_tmp_seq                    <= 4'h0;
    rf_rx_init_status               <= HMC_DOWN;
    rf_link_up                      <= LINK_DOWN;
    rf_descramblers_locked          <= {NUM_LANES{1'b0}};

end
else begin

    rf_descramblers_locked  <= run_rx ? init_descrambler_locked : {NUM_LANES{1'b0}};
    init_bit_slip           <= {NUM_LANES{1'b0}};
    init_bit_slip_part      <= {NUM_LANES{1'b0}};
    phy_bit_slip            <= init_bit_slip | init_bit_slip_part;
    init_tmp_seq            <= init_tmp_seq + INIT_SEQ_INC_PER_CYCLE;

    init_bit_slip_cnt   <= init_bit_slip_cnt +1;

    case (rf_rx_init_status)
        HMC_DOWN: begin
            init_descrambler_aligned         <= {NUM_LANES{1'b0}};
            init_descrambler_part_aligned    <= {NUM_LANES{1'b0}};
            if(&rf_descramblers_locked) begin
                rf_rx_init_status <= HMC_WAIT_FOR_NULL;
            end
        end
        HMC_WAIT_FOR_NULL: begin
            if(|init_valid_flit_src == 1'b0) begin
                rf_rx_init_status <= HMC_NULL;
            end
        end
        HMC_NULL: begin
            if(&init_valid_flit_src) begin
                rf_rx_init_status      <= HMC_TS1_PART_ALIGN;
            end
        end
        HMC_TS1_PART_ALIGN: begin
            if(|init_bit_slip_cnt[RX_BIT_SLIP_CNT_LOG-1:LOG_NUM_LANES] == 1'b0)begin
                init_bit_slip_part[init_lane_cnt]                <= ~init_lane_has_correct_ts1[init_lane_cnt];
                init_descrambler_part_aligned[init_lane_cnt]     <= init_lane_has_correct_ts1[init_lane_cnt];
            end
            if(&init_descrambler_part_aligned/*=={NUM_LANES{1'b1}}*/) begin
                rf_rx_init_status   <= HMC_TS1_FIND_REF;
                init_tmp_seq        <= descrambled_data_per_lane[0][3:0] + INIT_SEQ_INC_PER_CYCLE;
                init_bit_slip_cnt   <= {RX_BIT_SLIP_CNT_LOG{1'b0}};
            end        
        end
        HMC_TS1_FIND_REF: begin
            if(init_seq_diff < 2)
                init_tmp_seq <= descrambled_data_per_lane[init_lane_cnt][3:0] + INIT_SEQ_INC_PER_CYCLE;
            
            if(&init_bit_slip_cnt==1'b1)
                rf_rx_init_status   <= HMC_TS1_ALIGN;

        end
        HMC_TS1_ALIGN: begin
            
            if(|init_bit_slip_cnt[RX_BIT_SLIP_CNT_LOG-1:LOG_NUM_LANES] == 1'b0)begin
                if(|init_seq_diff==1'b0 && init_lane_has_correct_ts1[init_lane_cnt])begin
                    init_descrambler_aligned[init_lane_cnt] <= 1'b1;
                end else begin
                    init_bit_slip[init_lane_cnt] <= 1'b1;
                end
            end

            if(rf_all_descramblers_aligned) begin
                rf_rx_init_status  <= HMC_NULL_NEXT;
            end  
        end
        HMC_NULL_NEXT: begin
             if(|init_valid_flit_src == 1'b0) begin
                rf_rx_init_status   <= HMC_UP;
                rf_link_up          <= LINK_UP;
            end             
        end

        HMC_UP: begin
            if(rf_hmc_sleep || !run_rx) begin
                rf_rx_init_status   <= HMC_DOWN;
                rf_link_up          <= LINK_DOWN;
            end
        end
    endcase
end
end

//========================================================================================================================================
//------------------------------------------------------------------Packet Processing
//========================================================================================================================================
//==================================================================================
//---------------------------------Detect HDR,Tail,Valid Flits and provide to CRC logic
//==================================================================================
always @(*)  begin
    //Use the remaining payload from last cycle
    data2crc_payload_remain_comb = data2crc_payload_remain;

    data2crc_hdr_comb    = {FPW{1'b0}};
    data2crc_tail_comb   = {FPW{1'b0}};
    data2crc_valid_comb  = {FPW{1'b0}};

    for(i_f=0;i_f<FPW;i_f=i_f+1) begin

        data2crc_lng_per_flit_comb[i_f] = 4'h0;

        
        case (data2crc_payload_remain_comb)
        4'h1: begin
            data2crc_tail_comb[i_f]      = 1'b1;
            data2crc_valid_comb[i_f]     = 1'b1;
            data2crc_payload_remain_comb = 4'h0;
        end
        4'h0: begin
            if(valid_flit_src[i_f])begin
                data2crc_hdr_comb[i_f]   = 1'b1;
                data2crc_valid_comb[i_f] = 1'b1;
                if(lng(d_in_flit[i_f])<2 || lng(d_in_flit[i_f])>9 || !lng_dln_equal(d_in_flit[i_f]))begin
                    data2crc_lng_per_flit_comb[i_f] = 4'h1;
                    data2crc_tail_comb[i_f]         = 1'b1;
                    data2crc_payload_remain_comb    = 4'h0;
                end else begin
                    data2crc_payload_remain_comb    = lng(d_in_flit[i_f]) -1;
                    data2crc_lng_per_flit_comb[i_f] = lng(d_in_flit[i_f]);
                end
            end
        end
        default: begin
            data2crc_valid_comb[i_f]     = 1'b1;
            data2crc_payload_remain_comb = data2crc_payload_remain_comb - 1;
        end
        endcase
    end
end

//Register the combinational logic from previous stage
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin

    data2crc_hdr             <= {FPW{1'b0}};
    data2crc_tail            <= {FPW{1'b0}};
    data2crc_valid           <= {FPW{1'b0}};
    data2crc_payload_remain  <= 4'h0;

    for(i_f=0;i_f<FPW;i_f=i_f+1) begin
        data2crc_lng_per_flit[i_f] <= 4'h0;
    end

end else begin
    if(rf_link_up) begin
        data2crc_valid  <= data2crc_valid_comb;
    end
    
    data2crc_hdr            <= data2crc_hdr_comb;
    data2crc_tail           <= data2crc_tail_comb;
    data2crc_payload_remain <= data2crc_payload_remain_comb;

    for(i_f=0;i_f<FPW;i_f=i_f+1) begin
        data2crc_lng_per_flit[i_f] <= data2crc_lng_per_flit_comb[i_f];
    end
end
end

//====================================================================
//---------------------------------IRTRY Stage
//====================================================================
//-- Count all types of IRTRY packets
always @(*)  begin

    flit_after_irtry_stage_is_start_retry_comb = {FPW{1'b0}};
    flit_after_irtry_stage_is_clear_error_comb = {FPW{1'b0}};

    irtry_clear_error_cnt_comb = irtry_clear_error_cnt;
    irtry_start_retry_cnt_comb = irtry_start_retry_cnt;


    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin

        if( crc_d_out_flit_is_flow[i_f] &&
            cmd(crc_d_out_flit[i_f]) == {CMD_IRTRY} &&
            !crc_d_out_flit_is_error[i_f]
        ) begin

            if(irtry_start_retry_flag(crc_d_out_flit[i_f])) begin
                //it's a start tx retry pkt
                irtry_start_retry_cnt_comb   = irtry_start_retry_cnt_comb + 5'h1;
                irtry_clear_error_cnt_comb   = 5'h0;
            end else begin
                //must be clear error pkt
                irtry_clear_error_cnt_comb   = irtry_clear_error_cnt_comb + 5'h1;
                irtry_start_retry_cnt_comb   = 5'h0;
            end

            if(irtry_start_retry_cnt_comb == rf_irtry_received_threshold) begin
                //The start retry packet that reaches the trehold is treated as valid and will trigger tx retry
                flit_after_irtry_stage_is_start_retry_comb[i_f] = 1'b1;
            end

            //Clear error abort when threshold reached, allow following FLITs to be valid
            if(irtry_clear_error_cnt_comb == rf_irtry_received_threshold) begin
                flit_after_irtry_stage_is_clear_error_comb[i_f] = 1'b1;
            end

        end else begin
            //Reset both counters when received a non-irtry packet
            irtry_start_retry_cnt_comb = 5'h0;
            irtry_clear_error_cnt_comb = 5'h0;
        end
    end
end

//Save the temporary counts to be re-used in the next cycle and register the clear trigger
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin
    irtry_clear_trig      <= 1'b0;

    irtry_clear_error_cnt <= {5{1'b0}};
    irtry_start_retry_cnt <= {5{1'b0}};

end else begin
    irtry_clear_trig      <= |flit_after_irtry_stage_is_clear_error_comb;

    irtry_clear_error_cnt <= irtry_clear_error_cnt_comb;
    irtry_start_retry_cnt <= irtry_start_retry_cnt_comb;
end
end

//Propagate data and apply the valid masks
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    for(i_f = 0;i_f<(FPW);i_f=i_f+1) begin
        `ifdef RESET_ALL
        if(!res_n) flit_after_irtry_stage[i_f]  <= {128{1'b0}};
        else
        `endif
        flit_after_irtry_stage[i_f] <= crc_d_out_flit[i_f];
    end

if(!res_n) begin
    `ifdef RESET_ALL
        flit_after_irtry_stage_is_hdr         <= {FPW{1'b0}};
        flit_after_irtry_stage_is_tail        <= {FPW{1'b0}};
        flit_after_irtry_stage_is_poisoned    <= {FPW{1'b0}};
        flit_after_irtry_stage_has_rtc        <= {FPW{1'b0}};
        flit_after_irtry_stage_is_error       <= {FPW{1'b0}};
        flit_after_irtry_stage_is_valid       <= {FPW{1'b0}};
    `endif
    flit_after_irtry_stage_is_start_retry <= {FPW{1'b0}};
    flit_after_irtry_stage_is_clear_error <= {FPW{1'b0}};
end else begin

    flit_after_irtry_stage_is_start_retry <= flit_after_irtry_stage_is_start_retry_comb;
    flit_after_irtry_stage_is_clear_error <= flit_after_irtry_stage_is_clear_error_comb;
end
    flit_after_irtry_stage_is_hdr         <= crc_d_out_flit_is_hdr;
    flit_after_irtry_stage_is_tail        <= crc_d_out_flit_is_tail;
    flit_after_irtry_stage_is_poisoned    <= crc_d_out_flit_is_poisoned; 
    flit_after_irtry_stage_has_rtc        <= crc_d_out_flit_has_rtc;
    flit_after_irtry_stage_is_error       <= crc_d_out_flit_is_error;
    flit_after_irtry_stage_is_valid       <= crc_d_out_flit_is_valid; 
end

//-------------------------------------------Error abort mode
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin

    //TX signaling
    tx_error_abort_mode             <= 1'b0;
    tx_error_abort_mode_cleared     <= 1'b0;

end else begin

    tx_error_abort_mode_cleared <= 1'b0;

    if(irtry_clear_trig) begin
        tx_error_abort_mode         <= 1'b0;
        tx_error_abort_mode_cleared <= 1'b1;
    end

    //Set error abort mode again if error detected
    if(|crc_d_out_flit_is_error || flit_after_seq_check_is_error)begin
        tx_error_abort_mode <= 1'b1;
    end

end
end

//==================================================================================
//---------------------------------SEQ check
//==================================================================================
//Check the seqnum FLIT by FLIT. Assign the last received seqnum when error abort mode is cleared
//!Lots of logic levels for 8FLIT config
always @(*)  begin

    next_seqnum_comb                    = 3'h0;
    flit_after_seq_check_is_error_comb  = {FPW{1'b0}};

    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        if(flit_after_irtry_stage_has_rtc[i_f]) begin
        //All packets that have an RTC also have a valid seqnum
            next_seqnum_comb = next_seqnum_comb + 3'h1;
            if(seq(flit_after_irtry_stage[i_f]) != (next_seqnum + next_seqnum_comb)) begin
                flit_after_seq_check_is_error_comb[i_f]  = 1'b1;
            end
        end
    end
end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    
    for(i_f = 0;i_f<(FPW);i_f=i_f+1) begin
        `ifdef RESET_ALL
        if(!res_n) flit_after_seq_check[i_f]  <= {128{1'b0}};
        else
        `endif
        flit_after_seq_check[i_f] <= flit_after_irtry_stage[i_f];
    end

if(!res_n) begin

    next_seqnum                         <= 3'h0;

    `ifdef RESET_ALL
        flit_after_seq_check_is_hdr         <= {FPW{1'b0}};
        flit_after_seq_check_is_tail        <= {FPW{1'b0}};
        flit_after_seq_check_is_valid       <= {FPW{1'b0}};
        flit_after_seq_check_is_poisoned    <= {FPW{1'b0}};
        flit_after_seq_check_has_rtc        <= {FPW{1'b0}};
        flit_after_seq_check_is_start_retry <= {FPW{1'b0}};
        flit_after_seq_check_is_clear_error <= {FPW{1'b0}};
    `endif
    flit_after_seq_check_is_error       <= {FPW{1'b0}};
end else begin

    //Set the expected sequence number to the first one after error abort mode was cleared
    //otherwise apply the last seqnum + combinatioanl offset
    if(|flit_after_irtry_stage_is_clear_error_comb) begin
        next_seqnum     <= first_seq_after_error + next_seqnum_comb;
    end else begin
        next_seqnum     <= next_seqnum + next_seqnum_comb;
    end

    //propage data to next stage and include any error bits that were detected during sequence number check
    flit_after_seq_check_is_error       <= flit_after_irtry_stage_is_error |
                                           flit_after_seq_check_is_error_comb;

end
    flit_after_seq_check_is_hdr         <= flit_after_irtry_stage_is_hdr;
    flit_after_seq_check_is_tail        <= flit_after_irtry_stage_is_tail;
    flit_after_seq_check_is_valid       <= flit_after_irtry_stage_is_valid;
    flit_after_seq_check_is_poisoned    <= flit_after_irtry_stage_is_poisoned;
    flit_after_seq_check_has_rtc        <= flit_after_irtry_stage_has_rtc;
    flit_after_seq_check_is_start_retry <= flit_after_irtry_stage_is_start_retry; 
    flit_after_seq_check_is_clear_error <= flit_after_irtry_stage_is_clear_error; 
end

//==================================================================================
//---------------------------------Valid Mask - Remove valid bits for invalid FLITs
//==================================================================================
always@(*) begin
    flit_after_mask_stage_is_valid_mask_lsb = {FPW{1'b0}}; 
    flit_after_mask_stage_is_valid_mask_msb = {FPW{1'b0}}; 
    for(i_f = FPW-1; i_f >=0; i_f = i_f - 1) begin
        if(flit_after_seq_check_is_clear_error[i_f]) begin
            flit_after_mask_stage_is_valid_mask_msb       = {{FPW-1{1'b1}},1'b0} << i_f;
        end
        if(flit_after_seq_check_is_error[i_f]) begin
            flit_after_mask_stage_is_valid_mask_lsb       = {FPW{1'b1}} >> (FPW-i_f);
        end
    end

end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    
    for(i_f = 0;i_f<(FPW);i_f=i_f+1) begin
        flit_after_mask_stage[i_f] <= flit_after_seq_check[i_f];
    end

if(!res_n) begin

    `ifdef RESET_ALL
        flit_after_mask_stage_is_hdr         <= {FPW{1'b0}};
        flit_after_mask_stage_is_tail        <= {FPW{1'b0}};
        flit_after_mask_stage_is_poisoned    <= {FPW{1'b0}};
        flit_after_mask_stage_has_rtc        <= {FPW{1'b0}};
        flit_after_mask_stage_is_error       <= {FPW{1'b0}};
        flit_after_mask_stage_is_start_retry <= 1'b0;
    `endif
    flit_after_mask_stage_is_valid  <= {FPW{1'b0}};
    error                           <= 1'b0;
end else begin

    if(|flit_after_seq_check_is_clear_error)
        error <= 1'b0;

    if(|flit_after_seq_check_is_error)
        error <= 1'b1; 

    casex({error,|flit_after_seq_check_is_clear_error,|flit_after_seq_check_is_error})
        3'b000: begin
            flit_after_mask_stage_is_valid <= flit_after_seq_check_is_valid;
        end
        3'b001: begin
            flit_after_mask_stage_is_valid <= flit_after_seq_check_is_valid & flit_after_mask_stage_is_valid_mask_lsb;
        end
        3'bx10: begin
            flit_after_mask_stage_is_valid <= flit_after_seq_check_is_valid & flit_after_mask_stage_is_valid_mask_msb;
        end
        3'bx11: begin
            flit_after_mask_stage_is_valid <= flit_after_seq_check_is_valid & flit_after_mask_stage_is_valid_mask_msb & flit_after_mask_stage_is_valid_mask_lsb;
        end
        default: begin
            flit_after_mask_stage_is_valid <= {FPW{1'b0}};
        end
    endcase

    //propage data to next stage and include any error bits that were detected

end
    flit_after_mask_stage_is_hdr         <= flit_after_seq_check_is_hdr;
    flit_after_mask_stage_is_tail        <= flit_after_seq_check_is_tail;
    flit_after_mask_stage_is_poisoned    <= flit_after_seq_check_is_poisoned;
    flit_after_mask_stage_has_rtc        <= flit_after_seq_check_has_rtc;
    flit_after_mask_stage_is_error       <= flit_after_seq_check_is_error & flit_after_seq_check_is_tail;
    flit_after_mask_stage_is_start_retry <= flit_after_seq_check_is_start_retry;
end

//==================================================================================
//---------------------------------Tokens/Pointers/Sequence numbers
//==================================================================================
//Count Tokens that were returned
always @(*)  begin
    rtc_sum_comb                  = {MAX_RTC_RET_LOG{1'b0}};
    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        if(flit_after_mask_stage_has_rtc[i_f] && flit_after_mask_stage_is_valid[i_f])begin
            rtc_sum_comb                  =  rtc_sum_comb + rtc(flit_after_mask_stage[i_f]);
        end
    end
end

//Extract FRP/RRP + last seq (which is necessary to check packets after error_abort_mode is cleared)
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin

    tx_hmc_frp                      <= {8{1'b0}};
    tx_rrp                          <= {8{1'b0}};
    tx_returned_tokens              <= {MAX_RTC_RET_LOG{1'b0}};
    first_seq_after_error           <= 3'h0;
    tx_link_retry                   <= 1'b0;

end else begin
    //Return tokens
    tx_returned_tokens              <= rtc_sum_comb;

    //Process FLITs and extract frp/seq/rrp if applicable
    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin

        if((flit_after_mask_stage_is_tail[i_f] && flit_after_mask_stage_is_valid[i_f]) || flit_after_mask_stage_is_start_retry[i_f]) begin
            tx_rrp                  <=  rrp(flit_after_mask_stage[i_f]);
        end

        if(flit_after_mask_stage_has_rtc[i_f] && flit_after_mask_stage_is_valid[i_f])begin
            tx_hmc_frp                      <= frp(flit_after_mask_stage[i_f]);
            first_seq_after_error           <= seq(flit_after_mask_stage[i_f]);
        end
    end

    //-------------------------------------------TX retry
    tx_link_retry   <= 1'b0;

    if(|flit_after_mask_stage_is_start_retry)begin
        tx_link_retry              <= 1'b1;
    end

end
end

//==================================================================================
//---------------------------------Retrieve the lengths to invalidate FLITs
//==================================================================================
always @(*)  begin
//Retrieve the length from the header and assign it to the tail. This information will be used in the
//invalidation stage to mask out FLITs that belong to the faulty packet

    lng_comb = lng_temp;

    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin

        if(flit_after_seq_check_is_hdr[i_f]) begin
            if(flit_after_seq_check_is_error[i_f]) begin
                lng_comb = 4'h1;
            end else begin
                lng_comb = lng(flit_after_seq_check[i_f]);
            end
        end

        if(flit_after_seq_check_is_tail[i_f]) begin
            lng_per_tail_comb[i_f] = lng_comb;
        end else begin
            lng_per_tail_comb[i_f] = 4'h0;
        end

    end
end

//Register combinational values
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin
    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        lng_per_tail[i_f] <= 0;
    end
    lng_temp    <= 4'h0;
end else begin
    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        lng_per_tail[i_f] <= lng_per_tail_comb[i_f];
    end
    lng_temp    <= lng_comb;
end
end

//==================================================================================
//---------------------------------FLIT Invalidation Stage
//==================================================================================
//Constant propagation for some parts of the invalidation stage
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    `ifdef RESET_ALL
    if(!res_n) begin
        flit_in_invalidation_data[0]            <= {DWIDTH{1'b0}};

        for(i_c=0; i_c<(CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c=i_c+1) begin
            flit_in_invalidation_data[i_c+1]    <= {DWIDTH{1'b0}};
        end
    end else 
    `endif
    begin
        flit_in_invalidation_data[0]            <= flit_after_mask_stage_word;

        for(i_c=0; i_c<(CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c=i_c+1) begin
            flit_in_invalidation_data[i_c+1]        <= flit_in_invalidation_data[i_c];
        end
    end

    flit_in_invalidation_is_hdr[0]          <= flit_after_mask_stage_is_hdr;
    flit_in_invalidation_is_tail[0]         <= flit_after_mask_stage_is_tail;

    for(i_c=0; i_c<(CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c=i_c+1) begin
        flit_in_invalidation_is_hdr[i_c+1]          <= flit_in_invalidation_is_hdr[i_c];
        flit_in_invalidation_is_tail[i_c+1]         <= flit_in_invalidation_is_tail[i_c];
    end
end

//Mark all poisoned FLITs
always @(*)  begin
    flit_in_invalidation0_is_poisoned_comb  = {FPW{1'b0}};
    for(i_f = FPW-1; i_f>=0; i_f = i_f-1) begin
        if(flit_after_mask_stage_is_poisoned[i_f])begin
            flit_in_invalidation0_is_poisoned_comb =flit_in_invalidation0_is_poisoned_comb | 
                                                    (({FPW{1'b1}} >> (FPW-i_f-1)) & ~({FPW{1'b1}} >> lng_per_tail[i_f]+(FPW-i_f-1)));
        end
    end
end
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin

    for(i_c = 0; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET); i_c = i_c + 1) begin
        flit_in_invalidation_is_poisoned[i_c]  <= {FPW{1'b0}};
    end

end else begin
    flit_in_invalidation_is_poisoned[0]     <= flit_in_invalidation0_is_poisoned_comb;

    for(i_c = 0; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c = i_c + 1) begin
        flit_in_invalidation_is_poisoned[i_c+1] <= flit_in_invalidation_is_poisoned[i_c];
    end

    //If there is a poisoned packet mark all FLITs as such
    for(i_f = FPW-1; i_f>=0; i_f = i_f-1) begin
        if(flit_after_mask_stage_is_poisoned[i_f]) begin

            for(i_c = 0; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c = i_c + 1) begin
                if(lng_per_tail[i_f] > ((i_c)*FPW)+i_f+1) begin
                    flit_in_invalidation_is_poisoned[i_c+1] <= flit_in_invalidation_is_poisoned[i_c] | ~({FPW{1'b1}} >> lng_per_tail[i_f]-(i_c*FPW)-i_f-1);
                end
            end

        end
    end
end
end


//Invalidate FLITs that belong to errorenous packets
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin

    for(i_c = 0; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET); i_c = i_c + 1) begin
        flit_in_invalidation_is_valid[i_c]     <= {FPW{1'b0}};
    end
    flit_in_invalidation_mask_error <= {FPW{1'b0}};

end else begin

    //Reset the masks for invalidation stages
    flit_in_invalidation_mask_error         <= {FPW{1'b1}};

    //Propate invalidation stages but apply error and poisoned masks to the second stage
    for(i_c = 1; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c = i_c + 1) begin
        flit_in_invalidation_is_valid[i_c+1] <= flit_in_invalidation_is_valid[i_c];
    end
    flit_in_invalidation_is_valid[1] <= flit_in_invalidation_is_valid[0] & flit_in_invalidation_mask_error;

    //First apply valids from previous stage
    flit_in_invalidation_is_valid[0] <= flit_after_mask_stage_is_valid;

    //At least one FLIT contained an error in its tail. Leave all FLITs before the error untouched
    for(i_f = FPW-1; i_f>=0; i_f = i_f-1) begin
        if(flit_after_mask_stage_is_error[i_f]) begin
            flit_in_invalidation_mask_error <= {FPW{1'b1}} >> (FPW-i_f-1+lng_per_tail[i_f]);
        end

    //Now use the length of the packet to invalidate FLITs that may reside in the next stages already
        if(flit_after_mask_stage_is_error[i_f] && &flit_in_invalidation_mask_error) begin
            for(i_c = 0; i_c < (CYCLES_TO_COMPLETE_FULL_PACKET-1); i_c = i_c + 1) begin
                if(lng_per_tail[i_f] > ((i_c)*FPW)+i_f+1) begin
                    flit_in_invalidation_is_valid[i_c+1] <= flit_in_invalidation_is_valid[i_c] &
                                                            ({FPW{1'b1}} >> lng_per_tail[i_f]-(i_c*FPW)-i_f-1);
                end
            end
        end
    end

end
end

//==================================================================================
//---------------------------------Fill the input buffer with all response packets
//==================================================================================
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        `ifdef RESET_ALL
        if(!res_n) input_buffer_d_in_flit[i_f] <= {128{1'b0}};
        else
        `endif    
        input_buffer_d_in_flit[i_f]           <= checked_flit[i_f];
    end

    for(i_f=0;i_f<FPW;i_f=i_f+1) begin
        input_buffer_is_error_rsp[i_f]  <= checked_flit_is_hdr[i_f]     && cmd(checked_flit[i_f])==CMD_RSP_ERROR;
        input_buffer_is_hdr[i_f]        <= checked_flit_is_hdr[i_f]     && !checked_flit_is_poisoned[i_f] && !is_rsp_flow(checked_flit[i_f]);
        input_buffer_is_valid[i_f]      <= checked_flit_is_valid[i_f]   && !checked_flit_is_poisoned[i_f] && !(is_rsp_flow(checked_flit[i_f]) && checked_flit_is_hdr[i_f]);
        input_buffer_is_tail[i_f]       <= checked_flit_is_tail[i_f]    && !checked_flit_is_poisoned[i_f] && !(is_rsp_flow(checked_flit[i_f]) && checked_flit_is_hdr[i_f]);
    end

end
assign input_buffer_shift_in = |input_buffer_is_valid;

//==================================================================================
//---------------------------------Count responses and poisoned packets
//==================================================================================
always @(*)  begin
    rf_cnt_poisoned_comb = {LOG_FPW+1{1'b0}};
    rf_cnt_rsp_comb      = {LOG_FPW+1{1'b0}};

    for(i_f=0;i_f<(FPW);i_f=i_f+1) begin
        if(checked_flit_is_poisoned[i_f] && checked_flit_is_hdr[i_f])begin
            rf_cnt_poisoned_comb = rf_cnt_poisoned_comb + {{LOG_FPW{1'b0}},1'b1};
        end
        if(input_buffer_is_tail[i_f] && !input_buffer_is_error_rsp[i_f])begin
            //if its a tail but not error response
            rf_cnt_rsp_comb = rf_cnt_rsp_comb + {{LOG_FPW{1'b0}},1'b1};
        end
    end
end

`ifdef XILINX
    //Use the openhmc_counter48_wrapper_xilinx in building_blocks/counter to directly instantiate DSP48
    openhmc_counter48_wrapper_xilinx #(
        .INC_SIZE(LOG_FPW+1),
        .PIPELINED(XIL_CNT_PIPELINED)
    )cnt_poisoned (
        .clk(clk),
        .res_n(res_n),
        .inc_value(rf_cnt_poisoned_comb),
        .value(rf_cnt_poisoned)
    );

    openhmc_counter48_wrapper_xilinx #(
        .INC_SIZE(LOG_FPW+1),
        .PIPELINED(XIL_CNT_PIPELINED)
    )cnt_rsp (
        .clk(clk),
        .res_n(res_n),
        .inc_value(rf_cnt_rsp_comb),
        .value(rf_cnt_rsp)
    );

`else
    reg [RF_COUNTER_SIZE-1:0]   rf_cnt_poisoned_temp;
    reg [RF_COUNTER_SIZE-1:0]   rf_cnt_rsp_temp;
    assign rf_cnt_poisoned      = rf_cnt_poisoned_temp;
    assign rf_cnt_rsp           = rf_cnt_rsp_temp;

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    if(!res_n) begin
        rf_cnt_poisoned_temp <= {RF_COUNTER_SIZE{1'b0}};
        rf_cnt_rsp_temp      <= {RF_COUNTER_SIZE{1'b0}};
    end else begin
        rf_cnt_poisoned_temp <= rf_cnt_poisoned_temp + {{RF_COUNTER_SIZE-LOG_FPW-1{1'b0}},rf_cnt_poisoned_comb};
        rf_cnt_rsp_temp      <= rf_cnt_rsp_temp + {{RF_COUNTER_SIZE-LOG_FPW-1{1'b0}},rf_cnt_rsp_comb};
    end
    end
`endif 


//==================================================================================
//---------------------------------Return the tokens
//==================================================================================
generate
    if(OPEN_RSP_MODE==0) begin : return_tokens

    reg   [MAX_RTC_RET_LOG-1:0] rtc_returned_tokens;
    reg   [MAX_RTC_RET_LOG-1:0] rtc_poisoned_tokens_to_return;
    reg   [LOG_FPW:0]           tokens_out_of_fifo_sum_comb;
    reg   [LOG_FPW:0]           tokens_poisoned;

    assign tx_hmc_tokens_to_return          = rtc_returned_tokens;
    assign tx_hmc_poisoned_tokens_to_return = rtc_poisoned_tokens_to_return;

        //Poisoned tokens will be returned before they enter the input buffer
        always @(*)  begin
            tokens_poisoned          = {LOG_FPW+1{1'b0}};

            for(i_f=0; i_f<FPW; i_f=i_f+1) begin
                tokens_poisoned  =   tokens_poisoned + checked_flit_is_poisoned[i_f];
            end
        end

        //All other tokens will be returned as they leave the input buffer
        always @(*)  begin
            tokens_out_of_fifo_sum_comb          = {LOG_FPW+1{1'b0}};

            if(input_buffer_shift_out)begin
                for(i_f=0; i_f<FPW; i_f=i_f+1) begin
                    tokens_out_of_fifo_sum_comb  =   tokens_out_of_fifo_sum_comb + 
                                                     (input_buffer_d_out[DWIDTH+i_f] && 
                                                     !input_buffer_d_out[DWIDTH+i_f+(3*FPW)]);    //increment if there's a valid FLIT, but not an error response
                end
            end
        end

        `ifdef ASYNC_RES
        always @(posedge clk or negedge res_n)  begin `else
            always @(posedge clk)  begin `endif
            if(!res_n) begin
                rtc_returned_tokens            <= {LOG_FPW+1{1'b0}};
                rtc_poisoned_tokens_to_return  <= {LOG_FPW+1{1'b0}};
            end else begin
                rtc_returned_tokens            <= tokens_out_of_fifo_sum_comb;
                rtc_poisoned_tokens_to_return  <= tokens_poisoned;
            end
        end

    end else begin
        //no input buffer, and no tokens will be returned
        assign tx_hmc_tokens_to_return          = {LOG_FPW+1{1'b0}};
        assign tx_hmc_poisoned_tokens_to_return = {LOG_FPW+1{1'b0}}; 
    end
endgenerate



//==================================================================================
//---------------------------------Shift response packets into the output fifo
//==================================================================================
generate
    if(OPEN_RSP_MODE==0) begin : assign_output_data

    reg   [DWIDTH-1:0]          out_data;
    reg                         out_shift_in;
    reg   [4*FPW-1:0]           out_ctrl;

    assign d_out_fifo_data      = out_data;
    assign d_out_fifo_shift_in  = out_shift_in;
    assign d_out_fifo_ctrl      = out_ctrl;

        `ifdef ASYNC_RES
        always @(posedge clk or negedge res_n)  begin `else
        always @(posedge clk)  begin `endif
            if(!res_n) begin
                //----FIFO
                out_shift_in          <= 1'b0;
                out_ctrl              <= {4*FPW{1'b0}};
                out_data              <= {DWIDTH{1'b0}};
            end else begin
                if(input_buffer_shift_out)begin
                    out_shift_in         <= 1'b1;
                    out_ctrl             <= input_buffer_d_out[DWIDTH+(4*FPW)-1:DWIDTH];
                    out_data             <= input_buffer_d_out[DWIDTH-1:0];
                end else begin
                    out_shift_in          <= 1'b0;
                end
            end
        end
    end else begin  //Open Response Mode

    assign d_out_fifo_data      = input_buffer_d_in[DWIDTH-1:0];
    assign d_out_fifo_shift_in  = input_buffer_shift_in;
    assign d_out_fifo_ctrl      = input_buffer_d_in[DWIDTH+(4*FPW)-1:DWIDTH];

    end
endgenerate



//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

wire   lanes_can_lock;
assign lanes_can_lock = (rf_hmc_sleep || !run_rx) ? 1'b0 : 1'b1;
// 
//Lane Init
genvar i;
generate
for(i=0;i<NUM_LANES;i=i+1)begin : lane_gen
    rx_lane_logic #(
        .DWIDTH(DWIDTH),
        .NUM_LANES(NUM_LANES),
        .CTRL_LANE_POLARITY(CTRL_LANE_POLARITY),
        .BITSLIP_SHIFT_RIGHT(BITSLIP_SHIFT_RIGHT)
    ) rx_lane_I (
        .clk(clk),
        .res_n(res_n),
        .can_lock(lanes_can_lock),
        .bit_slip(phy_bit_slip[i]),
        .descrambler_locked(init_descrambler_locked[i]),
        .descrambler_disable(rf_scrambler_disable),
        .lane_polarity(rf_lane_polarity[i]),
        .scrambled_data_in(phy_scrambled_data_in[i*WIDTH_PER_LANE+WIDTH_PER_LANE-1:i*WIDTH_PER_LANE]),
        .descrambled_data_out(descrambled_data_per_lane[i])
    );
end
endgenerate

//HMC CRC Logic
rx_crc_compare #(
    .DWIDTH(DWIDTH),
    .FPW(FPW),
    .LOG_FPW(LOG_FPW)
)
rx_crc_compare
(
    .clk(clk),
    .res_n(res_n),
    //input
    .d_in_data(d_in_dly),
    .d_in_hdr(data2crc_hdr),
    .d_in_tail(data2crc_tail),
    .d_in_valid(data2crc_valid),
    // .d_in_error(data2crc_error),
    .d_in_lng(data2crc_lng),
    //output
    .d_out_data(crc_d_out_data),
    .d_out_hdr(crc_d_out_flit_is_hdr),
    .d_out_tail(crc_d_out_flit_is_tail),
    .d_out_valid(crc_d_out_flit_is_valid),
    .d_out_error(crc_d_out_flit_is_error),
    .d_out_poisoned(crc_d_out_flit_is_poisoned),
    .d_out_rtc(crc_d_out_flit_has_rtc),
    .d_out_flow(crc_d_out_flit_is_flow)
);

generate
    if(OPEN_RSP_MODE==0) begin : use_input_buffer
        //Buffer Fifo - Depth = Max Tokens
        openhmc_sync_fifo #(
                .DATASIZE(DWIDTH+(4*FPW)),   //+4*FPW for header/tail/valid/error response information -> AXI-4 TUSER signal
                .ADDRSIZE(LOG_MAX_RX_TOKENS)
            ) input_buffer_I(
                .clk(clk),
                .res_n(res_n),
                .d_in(input_buffer_d_in),
                .shift_in(input_buffer_shift_in),
                .d_out(input_buffer_d_out),
                .shift_out(input_buffer_shift_out),
                .empty(input_buffer_empty)
            );
    end
endgenerate

endmodule
`default_nettype wire
