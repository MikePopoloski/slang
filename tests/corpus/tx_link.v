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
 *  Module name: tx_link
 *
 */

`default_nettype none

module tx_link #(
    parameter LOG_FPW           = 2,
    parameter FPW               = 4,
    parameter DWIDTH            = FPW*128,
    parameter NUM_LANES         = 8,
    parameter RF_COUNTER_SIZE   = 64,
    parameter HMC_RX_AC_COUPLED = 1,
    parameter MAX_RTC_RET_LOG   = 8,
    parameter LOG_MAX_RX_TOKENS = 8,
    parameter LOG_MAX_HMC_TOKENS= 10,
    parameter LOG_IRTRY_TIMOUT  = 8,
    parameter XIL_CNT_PIPELINED = 0,
    //Debug
    parameter DBG_RX_TOKEN_MON  = 1,
    parameter OPEN_RSP_MODE     = 0
) (

    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    input   wire                        clk,
    input   wire                        res_n,

    //----------------------------------
    //----TO HMC PHY
    //----------------------------------
    output  wire [DWIDTH-1:0]           phy_scrambled_data_out,

    //----------------------------------
    //----HMC IF
    //----------------------------------
    output  reg                         LXRXPS,
    input   wire                        LXTXPS,

    //----------------------------------
    //----Input data
    //----------------------------------
    input   wire [DWIDTH-1:0]           d_in_data,
    input   wire [FPW-1:0]              d_in_flit_is_hdr,
    input   wire [FPW-1:0]              d_in_flit_is_tail,
    input   wire [FPW-1:0]              d_in_flit_is_valid,
    input   wire                        d_in_empty,
    input   wire                        d_in_a_empty,
    output  reg                         d_in_shift_out,

    //----------------------------------
    //----RX Block
    //----------------------------------
    input   wire                        rx_force_tx_retry,
    input   wire                        rx_error_abort_mode,
    input   wire                        rx_error_abort_mode_cleared,
    input   wire [7:0]                  rx_hmc_frp,
    input   wire [7:0]                  rx_rrp,
    input   wire [MAX_RTC_RET_LOG-1:0]  rx_returned_tokens,
    input   wire [LOG_FPW:0]            rx_hmc_tokens_to_return,
    input   wire [LOG_FPW:0]            rx_hmc_poisoned_tokens_to_return,

    //----------------------------------
    //----RF
    //----------------------------------
    //Monitoring    1-cycle set to increment
    output  reg                         rf_cnt_retry,
    output  wire [RF_COUNTER_SIZE-1:0]  rf_sent_p,
    output  wire [RF_COUNTER_SIZE-1:0]  rf_sent_np,
    output  wire [RF_COUNTER_SIZE-1:0]  rf_sent_r,
    output  reg                         rf_run_length_bit_flip,
    output  reg                         rf_error_abort_not_cleared,

    //Status
    input   wire                        rf_link_is_up,
    input   wire                        rf_hmc_received_init_null,
    input   wire                        rf_descramblers_aligned,
    output  wire [1:0]                  rf_tx_init_status,
    output  reg  [LOG_MAX_HMC_TOKENS-1:0]rf_hmc_tokens_av,
    output  wire [LOG_MAX_RX_TOKENS-1:0]rf_rx_tokens_av,

    //Control
    input   wire                        rf_hmc_sleep_requested,
    input   wire                        rf_warm_reset,
    input   wire                        rf_scrambler_disable,
    input   wire [LOG_MAX_RX_TOKENS-1:0]rf_rx_buffer_rtc,
    input   wire [4:0]                  rf_irtry_to_send,
    input   wire                        rf_run_length_enable

);

`include "hmc_field_functions.h"

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================
//------------------------------------------------------------------------------------General Assignments
localparam LANE_WIDTH       = (DWIDTH/NUM_LANES);

integer i_f;    //counts to FPW
integer i_t;    //counts to number of TS1 packets in a word

//Packet command 3-MSB definition
localparam PKT_WRITE        = 3'b001;
localparam PKT_MISC_WRITE   = 3'b010;
localparam PKT_READ         = 3'b110;
localparam PKT_MODE_READ    = 3'b101;
localparam PKT_P_WRITE      = 3'b011;
localparam PKT_MISC_P_WRITE = 3'b100;

localparam CMD_IRTRY        = 6'b000011;

//------------------------------------------------------------------------------------Scrambler
wire [14:0]             seed_lane   [NUM_LANES-1:0];

assign seed_lane[0]     = 15'h4D56;
assign seed_lane[1]     = 15'h47FF;
assign seed_lane[2]     = 15'h75B8;
assign seed_lane[3]     = 15'h1E18;
assign seed_lane[4]     = 15'h2E10;
assign seed_lane[5]     = 15'h3EB2;
assign seed_lane[6]     = 15'h4302;
assign seed_lane[7]     = 15'h1380;

generate
    if(NUM_LANES==16) begin : seed_gen_16x
        assign seed_lane[8]     = 15'h3EB3;
        assign seed_lane[9]     = 15'h2769;
        assign seed_lane[10]    = 15'h4580;
        assign seed_lane[11]    = 15'h5665;
        assign seed_lane[12]    = 15'h6318;
        assign seed_lane[13]    = 15'h6014;
        assign seed_lane[14]    = 15'h077B;
        assign seed_lane[15]    = 15'h261F;
    end
endgenerate

wire [NUM_LANES-1:0]    bit_was_flipped;

//------------------------------------------------------------------------------------FSM and States
reg [2:0]  state;
reg [1:0]  init_state;
localparam INIT_TX_NULL_1       = 2'b00;
localparam INIT_TX_TS1          = 2'b01;
localparam INIT_TX_NULL_2       = 2'b11;
localparam INIT_DONE            = 2'b10;

localparam INIT                 = 3'b000;
localparam IDLE                 = 3'b001;
localparam TX                   = 3'b010;
localparam HMC_RTRY             = 3'b011;
localparam SLEEP                = 3'b100;
localparam WAIT_FOR_HMC         = 3'b101;
localparam LNK_RTRY             = 3'b110;
localparam DEBUG                = 3'b111;

assign  rf_tx_init_status = init_state;

reg     rtc_rx_initialize;

//------------------------------------------------------------------------------------DATA and ORDERING
//reorder incoming data to FLITs
wire [127:0]   d_in_flit [FPW-1:0];
genvar  f;
generate
        for(f = 0; f < (FPW); f = f + 1) begin : reorder_input_data_to_flits
            assign d_in_flit[f] = d_in_data[127+(f*128):f*128];
        end
endgenerate

//Create a mask and an input buffer that is necessary if packet transmission is interrupted and packets remain untransmitted
reg                 d_in_use_buf;
reg  [127:0]        d_in_buf_flit          [FPW-2:0];
reg  [FPW-2:0]      d_in_buf_flit_is_hdr;
reg  [FPW-2:0]      d_in_buf_flit_is_valid;

//Reorder the data per lane
wire [DWIDTH-1:0]   data_rdy;
wire [DWIDTH-1:0]   data_to_scrambler;

genvar l,n;
generate
    for(n = 0; n < NUM_LANES; n = n + 1) begin : reorder_data_to_lanes
        for(l = 0; l < LANE_WIDTH; l = l + 1) begin
            assign data_to_scrambler[l+n*LANE_WIDTH] = data_rdy[l*NUM_LANES+n];
        end
    end
endgenerate

//------------------------------------------------------------------------------------Init Regs
localparam TS1_SEQ_INC_VAL_PER_CYCLE        = (NUM_LANES==8) ? FPW : (FPW/2);
localparam LOG_CYCLES_NULL_TO_SEND          = (FPW == 2) ? 4 :
                                              (FPW == 4) ? 3 :
                                              (FPW == 6) ? 3 :
                                              2;

wire  [(NUM_LANES*4)-1:0]       ts1_seq_part_reordered      [TS1_SEQ_INC_VAL_PER_CYCLE-1:0];    //ts1 seq is 4 bits
reg   [3:0]                     ts1_seq_nr_per_flit         [TS1_SEQ_INC_VAL_PER_CYCLE-1:0];
wire  [127:0]                   ts1_flit                    [FPW-1:0];
reg   [LOG_CYCLES_NULL_TO_SEND-1:0] num_null_cycles_sent;

generate
    for(f = 0; f < TS1_SEQ_INC_VAL_PER_CYCLE; f = f + 1) begin : generate_lane_dependent_ts1_sequence

        for(n=0; n<4; n=n+1) begin
            assign ts1_seq_part_reordered[f][(n*NUM_LANES)+NUM_LANES-1:(n*NUM_LANES)] = {NUM_LANES{ts1_seq_nr_per_flit[f][n]}};
        end

        if(NUM_LANES==8) begin
            assign ts1_flit[f] = {
                32'hffffffff,32'h0,1'h1,7'h0,7'b1111111,1'h0,7'h0,1'h1,1'h0,7'b1111111,ts1_seq_part_reordered[f]
            };
        end else begin
            assign ts1_flit[f*2+1] = {
                64'hffffffffffffffff,64'h0
            };
            assign ts1_flit[f*2] = {
                16'h8000,16'hfffe,16'h0001,16'h7fff,ts1_seq_part_reordered[f]
            };
        end

    end
endgenerate
//------------------------------------------------------------------------------------Counter variables
reg  [LOG_FPW:0]    rf_sent_p_comb;
reg  [LOG_FPW:0]    rf_sent_np_comb;
reg  [LOG_FPW:0]    rf_sent_r_comb;

//------------------------------------------------------------------------------------SEQ FRP RTC Stage
reg  [127:0]        data2rtc_stage_flit     [FPW-1:0];
reg  [FPW-1:0]      data2rtc_stage_flit_is_hdr;
reg  [FPW-1:0]      data2rtc_stage_flit_is_tail;
reg  [FPW-1:0]      data2rtc_stage_flit_is_valid;
reg                 data2rtc_stage_is_flow;
reg                 data2rtc_stage_force_tx_retry;

reg  [127:0]        data2seq_frp_stage_flit          [FPW-1:0];
reg  [FPW-1:0]      data2seq_frp_stage_flit_is_hdr;
reg  [FPW-1:0]      data2seq_frp_stage_flit_is_tail;
reg  [FPW-1:0]      data2seq_frp_stage_flit_is_valid;
reg                 data2seq_frp_stage_is_flow;
reg                 data2seq_frp_stage_force_tx_retry;

//Information used to fill the retry buffer
reg [LOG_FPW-1:0]   target_temp [FPW:0];
reg [LOG_FPW-1:0]   next_target;
reg [LOG_FPW-1:0]   target      [FPW-1:0];

reg [LOG_FPW:0]     tx_seqnum_inc;
reg [2:0]           tx_seqnum_temp [FPW-1:0];

//------------------------------------------------------------------------------------RETRY
//HMC
//Number of cycles to wait until start HMC retry is issued again (when RX error abort is not cleared)
reg  [LOG_IRTRY_TIMOUT-1:0] error_abort_mode_clr_cnt;
reg                         force_hmc_retry;
reg  [4:0]                  irtry_start_retry_cnt;
reg  [4:0]                  irtry_clear_error_cnt;
wire [63:0]                 irtry_hdr;
assign                      irtry_hdr = {6'h0,34'h0,9'h0,4'h1,4'h1,1'h0,6'b000011};

//------------------------------------------------------------------------------------Retry Buffer
localparam RAM_ADDR_SIZE   =   (FPW == 2) ? 7 :
                               (FPW == 4) ? 6 :
                               (FPW == 6) ? 5 :
                               (FPW == 8) ? 5 :
                               1;

reg  [127:0]                data2ram_flit           [FPW-1:0];
reg  [127:0]                data2ram_flit_temp      [FPW-1:0];
reg  [FPW-1:0]              data2ram_flit_is_hdr;
reg  [FPW-1:0]              data2ram_flit_is_tail;
reg  [FPW-1:0]              data2ram_flit_is_valid;
reg                         data2ram_force_tx_retry;

//Header/Tail fields, and at the same time form the RAM read pointer
reg  [RAM_ADDR_SIZE-1:0]    tx_frp_adr [FPW-1:0];
reg  [2:0]                  tx_seqnum;


reg [FPW-1:0]               ram_w_en ;
reg                         ram_r_en;
wire [RAM_ADDR_SIZE-1:0]    ram_w_addr_next;
assign                      ram_w_addr_next = tx_frp_adr[0] + 1;
reg  [RAM_ADDR_SIZE-1:0]    ram_r_addr_temp;
reg  [FPW-1:0]              ram_r_mask;
wire [128+3-1:0]            ram_r_data              [FPW-1:0];
reg  [128+3-1:0]            ram_w_data              [FPW-1:0];

wire  [RAM_ADDR_SIZE-1:0]   ram_r_addr;
assign                      ram_r_addr = rx_rrp[7:8-RAM_ADDR_SIZE];

//Avoid overwriting not acknowleged FLITs in the retry buffer
wire [RAM_ADDR_SIZE-1:0]    ram_result;
assign                      ram_result          = ram_r_addr - ram_w_addr_next;

//A safe value since ram_w_addr_next is calculated some cycles after packets were accepted
wire                        ram_full;
assign                      ram_full = (ram_result<9 && ram_result>0) ? 1'b1 : 1'b0 ;

//Regs for TX Link retry handling
reg                 tx_retry_finished;
reg                 tx_retry_ongoing;
reg                 tx_link_retry_request;  //Sample the retry request

//------------------------------------------------------------------------------------RRP Stage
reg  [127:0]        data2rrp_stage_flit           [FPW-1:0];
reg  [FPW-1:0]      data2rrp_stage_flit_is_hdr;
reg  [FPW-1:0]      data2rrp_stage_flit_is_tail;
reg  [FPW-1:0]      data2rrp_stage_flit_is_valid;

`ifdef SIMULATION
    //We dont want to crash a simulation run because PRETs are still travelling upon test completion, so we include a trigger to only send PRETs when necessary in simulation
    //In hardware, PRETs will be sent whenever there is no valid FLIT on position 0 -> reduces the overall pointer return delay
    reg  [7:0]  last_transmitted_rx_hmc_frp;
`else 
    reg         send_prets;
`endif

//------------------------------------------------------------------------------------CRC
reg  [127:0]        data2crc_flit           [FPW-1:0];
wire [DWIDTH-1:0]   data2crc;
reg  [FPW-1:0]      data2crc_flit_is_hdr;
reg  [FPW-1:0]      data2crc_flit_is_tail;

generate
    for(f = 0; f < (FPW); f = f + 1) begin : concatenate_flits_to_single_reg
        assign data2crc[(f*128)+127:(f*128)]  = data2crc_flit[f];
    end
endgenerate

//------------------------------------------------------------------------------------FLOW PACKETS
//TRET
wire    [63:0]              tret_hdr;
assign                      tret_hdr        = {6'h0,34'h0,9'h0,4'h1,4'h1,1'h0,6'b000010};
//PRET
wire    [63:0]              pret_hdr;
assign                      pret_hdr        = {6'h0,34'h0,9'h0,4'h1,4'h1,1'h0,6'b000001};

//------------------------------------------------------------------------------------RTC HANDLING
//Registers for the RTC field in request packets
reg                         rtc_return;
reg  [4:0]                  rtc_return_val;

//A safe value to not send more FLITs than the HMC can buffer
reg  [LOG_FPW-1:0]          num_flits_in_buf;
reg  [LOG_FPW:0]            num_flits_transmitted;
reg  [LOG_MAX_RX_TOKENS-1:0]remaining_tokens;
localparam TOKENS_THRESHOLD=   (FPW == 2) ? 11 :
                               (FPW == 4) ? 15 :
                               (FPW == 6) ? 23 :
                               (FPW == 8) ? 23 :
                               1;
wire                        hmc_tokens_av;
assign                      hmc_tokens_av = ((rf_hmc_tokens_av+num_flits_in_buf+rx_returned_tokens) > TOKENS_THRESHOLD) ? 1'b1 : 1'b0;

//Return a maximum of 31 tokens
wire [4:0]                  outstanding_tokens_to_return;
assign                      outstanding_tokens_to_return   = (OPEN_RSP_MODE==0) ? (remaining_tokens > 31 ? 31 : remaining_tokens[4:0]) : 5'h0;

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------LOGIC STARTS HERE---------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

//====================================================================
//---------------------------------MISC
//====================================================================
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin
    rf_run_length_bit_flip   <= 1'b0;
end else begin
    rf_run_length_bit_flip   <= |bit_was_flipped;
end
end

//====================================================================
//---------------------------------Monitor Remaining Tokens in the RX input buffer, just a debug help
//====================================================================
//Track the remaining tokens in the rx input buffer. This is optional since the HMC must make sure not to send more tokens than RX can buffer, useful for debugging
generate
if(DBG_RX_TOKEN_MON==1 && OPEN_RSP_MODE==0) begin : Tokens_in_RX_buf

    reg  [6:0]                  sum_requested_tokens;       //Count the amount of tokens requested from the HMC
    reg  [6:0]                  sum_requested_tokens_temp;  //Use this register for combinational logic

    always @(*)  begin
        sum_requested_tokens_temp   = {7{1'b0}};

        for(i_f=0;i_f<FPW;i_f=i_f+1) begin

            if(data2rtc_stage_flit_is_hdr[i_f] && data2rtc_stage_flit_is_valid[i_f]) begin

                if(cmd_type(data2rtc_stage_flit[i_f]) == PKT_READ ||
                   cmd_type(data2rtc_stage_flit[i_f]) == PKT_MODE_READ ) begin
                    //it is either a data read or mode read
                    sum_requested_tokens_temp    =  sum_requested_tokens_temp + num_requested_flits(data2rtc_stage_flit[i_f]);
                end else if(    (cmd_type(data2rtc_stage_flit[i_f]) == PKT_WRITE) ||
                                (cmd_type(data2rtc_stage_flit[i_f]) == PKT_MISC_WRITE) ) begin
                    //it is not a posted transaction, so 1 token will be returned as response
                    sum_requested_tokens_temp    = sum_requested_tokens_temp + 1;
                end

            end
        end
    end

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    if(!res_n) begin
        sum_requested_tokens <= {7{1'b0}};
    end else begin
        sum_requested_tokens <= sum_requested_tokens_temp;
    end
    end

    //Monitor remaining tokens in the openHMC RX input buffer
    reg [LOG_MAX_RX_TOKENS-1:0] rx_tokens_av;
    assign rf_rx_tokens_av = rx_tokens_av;

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    if(!res_n) begin
        rx_tokens_av     <= {LOG_MAX_RX_TOKENS{1'b0}};
    end else begin
        if(state==INIT_TX_NULL_1)begin
            //initialize token counts when HMC init is not done
            rx_tokens_av        <= rf_rx_buffer_rtc;
        end else begin
            //calculate remaining tokens in RX buffers
            rx_tokens_av        <= rx_tokens_av + rx_hmc_tokens_to_return - sum_requested_tokens;
        end
    end
    end

end else begin
    assign rf_rx_tokens_av = {LOG_MAX_RX_TOKENS{1'b0}};
end
endgenerate

//=======================================================================================================================
//---------------------------------ALL OTHER LOGIC HERE
//=======================================================================================================================
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    if(!res_n) begin

        //----Init Regs
        for(i_t=0;i_t<TS1_SEQ_INC_VAL_PER_CYCLE;i_t=i_t+1) begin    //set
            ts1_seq_nr_per_flit[i_t]<= i_t;
        end
        num_null_cycles_sent             <= {LOG_CYCLES_NULL_TO_SEND{1'b0}};

        //General
        init_state                  <= INIT_TX_NULL_1;
        rtc_rx_initialize           <= 1'b1;
    end
    else begin
        
        case(init_state)
            //---------------------------------INIT. Refer to Initialization section in the specification

            INIT_TX_NULL_1: begin
                //---init_state---
                if(rf_hmc_received_init_null)begin
                    init_state            <= INIT_TX_TS1;
                end

            end

            INIT_TX_TS1: begin

                rtc_rx_initialize   <= 1'b0;
                for(i_t=0;i_t<TS1_SEQ_INC_VAL_PER_CYCLE;i_t=i_t+1) begin
                    ts1_seq_nr_per_flit[i_t]    <= ts1_seq_nr_per_flit[i_t] + TS1_SEQ_INC_VAL_PER_CYCLE;
                end

                //---init_state---
                if(rf_descramblers_aligned)begin
                    init_state   <= INIT_TX_NULL_2;
                end

            end

            INIT_TX_NULL_2: begin
                //Issue at least 32 NULL FLITs before going active
                if(&num_null_cycles_sent && rf_link_is_up) begin
                        init_state <= INIT_DONE;
                end 
                num_null_cycles_sent <= num_null_cycles_sent + 1;
            end
            default: begin
            end
        endcase

        if(!LXTXPS || rf_warm_reset) begin
            init_state          <= INIT_TX_NULL_1;
            if(rf_warm_reset)
                rtc_rx_initialize   <= 1'b1;
        end

    end
end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

`ifdef RESET_ALL
    if(!res_n) begin
        for(i_f=0;i_f<FPW;i_f=i_f+1)    data2rtc_stage_flit[i_f] <= {128{1'b0}};
        for(i_f=0;i_f<FPW-1;i_f=i_f+1)  d_in_buf_flit[i_f]       <= {128{1'b0}};
    end else
`endif
begin    
    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        data2rtc_stage_flit[i_f]    <= {128{1'b0}};
    end

    case(state)

            INIT: begin
                if(init_state == INIT_TX_TS1) begin

                    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
                        data2rtc_stage_flit[i_f]    <= ts1_flit[i_f];
                    end
                end
            end

            IDLE: begin
                if(|remaining_tokens && !ram_full)begin
                    data2rtc_stage_flit[0]            <= {{64{1'b0}},tret_hdr};
                end
            end

            TX: begin
                //Choose the data source
                if(d_in_use_buf) begin
                    for(i_f=0;i_f<FPW-1;i_f=i_f+1) begin
                        data2rtc_stage_flit[i_f+1]        <= d_in_buf_flit[i_f];
                    end
                end else begin
                    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
                        data2rtc_stage_flit[i_f]        <= d_in_flit[i_f];
                    end
                end

                for(i_f=0;i_f<FPW-1;i_f=i_f+1)begin
                    //No matter what, fill the buffer
                    d_in_buf_flit[i_f]              <= d_in_flit[i_f+1];
                end
            end

            HMC_RTRY: begin
                for(i_f=0;i_f<FPW;i_f=i_f+1)begin //Send IRTRY start retry
                    data2rtc_stage_flit[i_f]        <= {48'h0,8'b00000001,8'h00,irtry_hdr};
                end
            end

            LNK_RTRY: begin
                    for(i_f=0;i_f<FPW;i_f=i_f+1)begin   //Send IRTRY clear error abort
                        data2rtc_stage_flit[i_f]        <= {48'h0,8'b00000010,8'h00,irtry_hdr};
                    end
            end
    endcase
end

if(!res_n) begin
    data2rtc_stage_flit_is_hdr      <= {FPW{1'b0}};
    data2rtc_stage_flit_is_tail     <= {FPW{1'b0}};
    data2rtc_stage_flit_is_valid    <= {FPW{1'b0}};
    data2rtc_stage_is_flow          <= 1'b0;

    data2rtc_stage_force_tx_retry   <= 1'b0;
    d_in_shift_out                  <= 1'b0;

    //----Reset the input buffer reg
    d_in_buf_flit_is_hdr            <= {FPW-1{1'b0}};
    d_in_buf_flit_is_valid          <= {FPW-1{1'b0}};
    d_in_use_buf                    <= 1'b0;

    //General
    state                           <= INIT;

    //Token Flow Control
    remaining_tokens                <= {LOG_MAX_RX_TOKENS{1'b0}};
    rtc_return_val                  <= {5{1'b0}};
    rtc_return                      <= 1'b0;

    //Retry
    irtry_start_retry_cnt       <= {5{1'b0}};
    irtry_clear_error_cnt       <= {5{1'b0}};

    //HMC Control
    LXRXPS                          <= 1'b1;

    //Flow Control
    tx_link_retry_request           <= 1'b0;

end
else begin
//====================================================================
//---------------------------------INIT
//====================================================================
    //Reset control signals
    d_in_shift_out              <= 1'b0;
    irtry_start_retry_cnt       <= {5{1'b0}};
    irtry_clear_error_cnt       <= {5{1'b0}};

    //HMC Control
    LXRXPS                      <= 1'b1;

    if(rx_force_tx_retry)begin
        tx_link_retry_request   <= 1'b1;
    end

    //RTC
    rtc_return       <= 1'b0;
    //Initialize rtc to be transmitted after reset and warm reset
    if(rtc_rx_initialize) begin
        remaining_tokens <= rf_rx_buffer_rtc;
    end else begin
        remaining_tokens <= remaining_tokens + rx_hmc_tokens_to_return + rx_hmc_poisoned_tokens_to_return;
    end

    //Reset information bits
    data2rtc_stage_flit_is_hdr     <= {FPW{1'b0}};
    data2rtc_stage_flit_is_tail    <= {FPW{1'b0}};
    data2rtc_stage_flit_is_valid   <= {FPW{1'b0}};
    data2rtc_stage_is_flow         <= 1'b0;
    data2rtc_stage_force_tx_retry  <= 1'b0;

    rtc_return_val      <= outstanding_tokens_to_return;

    case(state)

//====================================================================
//---------------------------------Normal operation (including init TRETs)
//====================================================================
// Some branches to other states may be removed in HMC_RTRY for instance.
// Saves logic if an additional cycle in IDLE is acceptable

        INIT: begin
            if(init_state==INIT_DONE) state <= IDLE;
        end

        IDLE: begin
        //Issue NULL Flits if there's nothing else to do

            //SEND TRET PACKET even if there are no tokens available
            if(|remaining_tokens && !ram_full)begin
                data2rtc_stage_flit_is_hdr[0]     <= 1'b1;
                data2rtc_stage_flit_is_tail[0]    <= 1'b1;
                data2rtc_stage_flit_is_valid[0]   <= 1'b1;

                remaining_tokens    <= remaining_tokens + rx_hmc_tokens_to_return + rx_hmc_poisoned_tokens_to_return - outstanding_tokens_to_return;
                rtc_return          <= 1'b1;
            end

            // //---State---
            if(force_hmc_retry) begin
                state <= HMC_RTRY;
            end else if(tx_link_retry_request) begin
                state <= LNK_RTRY;
            end else if(rf_hmc_sleep_requested) begin
                state <= SLEEP;
            end else if(!d_in_empty && !ram_full && hmc_tokens_av) begin
                state           <= TX;
                d_in_shift_out  <= ~d_in_use_buf;
            end

        end

        TX: begin
        //Get and transmit data

            //First set control signals
            d_in_use_buf    <= 1'b0;
            d_in_shift_out  <= 1'b1;

            //Fill the buffer
            d_in_buf_flit_is_hdr         <= d_in_flit_is_hdr[FPW-1:1];
            d_in_buf_flit_is_valid       <= d_in_flit_is_valid[FPW-1:1];

            //If there is data buffered - use it
            data2rtc_stage_flit_is_hdr   <= d_in_use_buf ? {d_in_buf_flit_is_hdr,1'b0}   : d_in_flit_is_hdr;
            data2rtc_stage_flit_is_tail  <= d_in_use_buf ? {FPW{1'b0}}                   : d_in_flit_is_tail;
            data2rtc_stage_flit_is_valid <= d_in_use_buf ? {d_in_buf_flit_is_valid,1'b0} : d_in_flit_is_valid;

            //Set RTC to be added in the next step
            if( |remaining_tokens &&
                (!d_in_use_buf && |d_in_flit_is_tail)
            ) begin
                remaining_tokens    <= remaining_tokens + rx_hmc_tokens_to_return + rx_hmc_poisoned_tokens_to_return - outstanding_tokens_to_return;
                rtc_return          <= 1'b1;
            end

            //Exit state if seen a tail and exit condition occured
            if(     ((!d_in_use_buf && |d_in_flit_is_tail)) &&
                    (force_hmc_retry || ram_full || tx_link_retry_request || !hmc_tokens_av || d_in_a_empty)) begin

                d_in_shift_out  <= 1'b0;


                case ({force_hmc_retry,tx_link_retry_request})
                    2'b00: state    <= IDLE;
                    2'b01: state    <= LNK_RTRY;
                    default: state  <= HMC_RTRY;
                endcase

                for(i_f=0;i_f<FPW;i_f=i_f+1)begin
                    if(!d_in_use_buf && d_in_flit_is_tail[i_f])begin
                        data2rtc_stage_flit_is_valid    <= {FPW{1'b1}} >> {FPW-1-i_f};
                    end
                end

                for(i_f=1;i_f<FPW;i_f=i_f+1)begin
                    if(d_in_flit_is_tail[i_f])begin
                        d_in_buf_flit_is_hdr            <= d_in_flit_is_hdr[FPW-1:1] & ({FPW-1{1'b1}} << i_f);
                        d_in_buf_flit_is_valid          <= d_in_flit_is_valid[FPW-1:1] & ({FPW-1{1'b1}} << i_f);
                    end
                end

                //Use buf next time TX state is entered if there is a packet pending
                if(!d_in_use_buf && (d_in_flit_is_hdr[FPW-1:1] > d_in_flit_is_tail[FPW-1:1]))begin
                    d_in_use_buf    <= 1'b1;
                end
            end
        end

    //---------------------------------An error in RX path occured - send irtry start packets
        HMC_RTRY: begin

            data2rtc_stage_is_flow          <= 1'b1;

            irtry_start_retry_cnt               <= irtry_start_retry_cnt + FPW;

            if(irtry_start_retry_cnt+FPW >= rf_irtry_to_send)begin
                irtry_start_retry_cnt           <= {5{1'b0}};
                state <= IDLE;
            end

        end


    //---------------------------------HMC sent start retry packets -
    //                                 re-send all valid packets in RAM after sending clear error packets
        LNK_RTRY: begin

            if(!tx_retry_ongoing && (tx_link_retry_request || |irtry_clear_error_cnt)) begin

                data2rtc_stage_is_flow          <= 1'b1;

                if(irtry_clear_error_cnt+FPW >= rf_irtry_to_send)begin
                    irtry_clear_error_cnt         <= {5{1'b0}};
                    data2rtc_stage_force_tx_retry <= 1'b1;
                end else begin
                    irtry_clear_error_cnt   <= irtry_clear_error_cnt + FPW;
                end
            end

            if(tx_retry_finished && !tx_link_retry_request) begin
                state <= IDLE;
            end

            if(!tx_retry_ongoing && !rx_force_tx_retry) begin
                tx_link_retry_request   <= 1'b0;
            end
        end

    //---------------------------------Power State Management
        SLEEP: begin

            if(rf_hmc_sleep_requested) begin
                LXRXPS          <= 1'b0;
            end else begin
                state           <= WAIT_FOR_HMC;
            end

        end

        WAIT_FOR_HMC: begin

            if(LXTXPS) begin
                state           <= INIT;
            end

        end

    endcase

    //Warm Reset
    if(rf_warm_reset) begin
        //in case of a warm reset request, continue at INIT_TX_NULL_2 sequence and intialize tokens to be returned
        state       <= INIT;
    end

end
end

//====================================================================
//---------------------------------HMC input buffer Token Handling
//====================================================================
//Count the tokens that were used and make sure the HMC has enough tokens in its input buffer left
//This always block remains combinational to save one cycle
always @(*)  begin

    num_flits_transmitted = {LOG_FPW+1{1'b0}};
    num_flits_in_buf      = {LOG_FPW{1'b0}};

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        if(d_in_flit_is_valid[i_f] && d_in_shift_out) begin
            num_flits_transmitted   = num_flits_transmitted + 1;
        end
    end
    for(i_f=0;i_f<FPW-1;i_f=i_f+1)begin
        if(d_in_buf_flit_is_valid[i_f] && d_in_use_buf) begin
            num_flits_in_buf = num_flits_in_buf + 1;
        end
    end
end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin
    rf_hmc_tokens_av    <= {LOG_MAX_HMC_TOKENS{1'b0}};
end else begin
    rf_hmc_tokens_av    <= rf_hmc_tokens_av + rx_returned_tokens - num_flits_transmitted;
end
end

//====================================================================
//---------------------------------Counter in the RF, currently only data transactions are counted
//====================================================================
always @(*) begin

    rf_sent_p_comb   = {LOG_FPW+1{1'b0}};
    rf_sent_np_comb  = {LOG_FPW+1{1'b0}};
    rf_sent_r_comb   = {LOG_FPW+1{1'b0}};

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        if(data2seq_frp_stage_flit_is_hdr[i_f])begin
        //split into independent cases to avoid dependencies
        //Instead of comparing the entire cmd field, try to reduce logic effort

            //All non-posted types have either bit 3 or 4 in the cmd set:
            if( data2seq_frp_stage_flit[i_f][3] ^ data2seq_frp_stage_flit[i_f][4] ) begin
                rf_sent_np_comb = rf_sent_np_comb + {{LOG_FPW{1'b0}},1'b1};
            end

            //Only reads have bit 4 and 5 set:
            if(data2seq_frp_stage_flit[i_f][4] && data2seq_frp_stage_flit[i_f][5] ) begin
                rf_sent_r_comb = rf_sent_r_comb + {{LOG_FPW{1'b0}},1'b1};
            end

            //Otherwise it's a posted write
            if(cmd_type(data2seq_frp_stage_flit[i_f])==PKT_P_WRITE)begin
                rf_sent_p_comb = rf_sent_p_comb + {{LOG_FPW{1'b0}},1'b1};
            end

        end
    end
end



`ifdef XILINX
    openhmc_counter48_wrapper_xilinx #(
        .INC_SIZE(LOG_FPW+1),
        .PIPELINED(XIL_CNT_PIPELINED)
    ) cnt_sent_p (
        .clk(clk),
        .res_n(res_n),
        .inc_value(rf_sent_p_comb),
        .value(rf_sent_p)
    );

    openhmc_counter48_wrapper_xilinx #(
        .INC_SIZE(LOG_FPW+1),
        .PIPELINED(XIL_CNT_PIPELINED)
    ) cnt_sent_np (
        .clk(clk),
        .res_n(res_n),
        .inc_value(rf_sent_np_comb),
        .value(rf_sent_np)
    );

    openhmc_counter48_wrapper_xilinx #(
        .INC_SIZE(LOG_FPW+1),
        .PIPELINED(XIL_CNT_PIPELINED)
    ) cnt_sent_r (
        .clk(clk),
        .res_n(res_n),
        .inc_value(rf_sent_r_comb),
        .value(rf_sent_r)
    );    
`else
    reg  [RF_COUNTER_SIZE-1:0]    rf_sent_p_temp;
    reg  [RF_COUNTER_SIZE-1:0]    rf_sent_np_temp;
    reg  [RF_COUNTER_SIZE-1:0]    rf_sent_r_temp;
    assign rf_sent_p            = rf_sent_p_temp;
    assign rf_sent_np           = rf_sent_np_temp;
    assign rf_sent_r            = rf_sent_r_temp;

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    if(!res_n) begin
        rf_sent_p_temp   <= {RF_COUNTER_SIZE{1'b0}};
        rf_sent_np_temp  <= {RF_COUNTER_SIZE{1'b0}};
        rf_sent_r_temp   <= {RF_COUNTER_SIZE{1'b0}};
    end else begin
        rf_sent_p_temp   <= rf_sent_p_temp  + {{RF_COUNTER_SIZE-LOG_FPW-1{1'b0}},rf_sent_p_comb};
        rf_sent_np_temp  <= rf_sent_np_temp + {{RF_COUNTER_SIZE-LOG_FPW-1{1'b0}},rf_sent_np_comb};
        rf_sent_r_temp   <= rf_sent_r_temp  + {{RF_COUNTER_SIZE-LOG_FPW-1{1'b0}},rf_sent_r_comb};
    end
    end
`endif 

//====================================================================
//---------------------------------HMC Retry Logic
//====================================================================
//Monitor RX error abort mode - if the timer expires send another series of start retry packets
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

if(!res_n) begin
    error_abort_mode_clr_cnt       <= {8{1'b0}};
    force_hmc_retry                <= 1'b0;
    rf_error_abort_not_cleared     <= 1'b0;
end else begin

    rf_error_abort_not_cleared     <= 1'b0;

    if(rx_error_abort_mode)begin
        error_abort_mode_clr_cnt   <= error_abort_mode_clr_cnt + 1; //decrement counter
    end

    if(rx_error_abort_mode_cleared) begin
        error_abort_mode_clr_cnt   <= {8{1'b0}};
    end

    if(&error_abort_mode_clr_cnt) begin
        rf_error_abort_not_cleared  <= 1'b1;
    end

    if((rx_error_abort_mode && state!=HMC_RTRY && |error_abort_mode_clr_cnt==1'b0) || (&error_abort_mode_clr_cnt))begin
        force_hmc_retry             <= 1'b1;

    end else begin
        if(state==HMC_RTRY)begin
            force_hmc_retry     <= 1'b0;
        end
    end

end
end

//====================================================================
//---------------------------------RTC Stage
//====================================================================
generate
if(OPEN_RSP_MODE==0) begin : RTC_stage
    reg  [4:0]      data2seq_frp_stage_flit_rtc     [FPW-1:0];
    reg             rtc_return_sent;

    always @(*)  begin
        rtc_return_sent = 0;

        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            if(data2rtc_stage_flit_is_tail[i_f] && !rtc_return_sent && rtc_return) begin
                //Return outstanding tokens, but only once per cycle
                data2seq_frp_stage_flit_rtc[i_f] = rtc_return_val;
                rtc_return_sent                  = 1'b1;
            end else begin
                data2seq_frp_stage_flit_rtc[i_f] = 5'h00;
            end
        end
    end

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        `ifdef ASYNC_RES
        if(!res_n)
            data2seq_frp_stage_flit[i_f]  <= {128{1'b0}};
        else 
        `endif
        begin  
            data2seq_frp_stage_flit[i_f]        <= data2rtc_stage_flit[i_f];
            if(data2rtc_stage_flit_is_tail[i_f]) begin
                data2seq_frp_stage_flit[i_f][64+31:64+27]   <= data2seq_frp_stage_flit_rtc[i_f];
            end
        end
    end
    end
end else begin

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            `ifdef ASYNC_RES
            if(!res_n)
                data2seq_frp_stage_flit[i_f]  <= {128{1'b0}};
            else 
            `endif
            begin        
                data2seq_frp_stage_flit[i_f]  <= data2rtc_stage_flit[i_f];
            end
        end
    end
end
endgenerate

    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n)  begin `else
    always @(posedge clk)  begin `endif
    `ifdef RESET_ALL
        if(!res_n) begin
            data2seq_frp_stage_flit_is_hdr    <= {FPW{1'b0}};
            data2seq_frp_stage_flit_is_tail   <= {FPW{1'b0}};
            data2seq_frp_stage_flit_is_valid  <= {FPW{1'b0}};
            data2seq_frp_stage_is_flow        <= 1'b0;
            data2seq_frp_stage_force_tx_retry <= 1'b0;
        end else 
    `endif
    begin
        data2seq_frp_stage_flit_is_hdr    <= data2rtc_stage_flit_is_hdr & data2rtc_stage_flit_is_valid;
        data2seq_frp_stage_flit_is_tail   <= data2rtc_stage_flit_is_tail & data2rtc_stage_flit_is_valid;
        data2seq_frp_stage_flit_is_valid  <= data2rtc_stage_flit_is_valid;
        data2seq_frp_stage_is_flow        <= data2rtc_stage_is_flow;
        data2seq_frp_stage_force_tx_retry <= data2rtc_stage_force_tx_retry;
    end
    end

//====================================================================
//---------------------------------Seqnum and FRP Stage
//====================================================================

always @(*)  begin
    tx_seqnum_inc  = {LOG_FPW{1'b0}};
    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        tx_seqnum_temp[i_f] = 0;
        if(data2seq_frp_stage_flit_is_tail[i_f])begin
            tx_seqnum_inc       = tx_seqnum_inc + 1;
            tx_seqnum_temp[i_f] = tx_seqnum + tx_seqnum_inc;
        end
    end

    target_temp[0] = next_target;

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        if(data2rtc_stage_flit_is_valid[i_f]) begin
             target_temp[i_f+1] = target_temp[i_f] + 1;
             if(target_temp[i_f+1]==FPW)
                target_temp[i_f+1]=0;
        end else begin
            target_temp[i_f+1] = target_temp[i_f];
        end
    end
end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
if(!res_n) begin
    //Reset the target RAM location and seqnum
    tx_seqnum   <= {LOG_FPW{1'b0}};
    next_target <= {LOG_FPW{1'b0}};
    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        target[i_f]   <= {FPW{1'b0}};
    end
end else begin
    tx_seqnum   <= tx_seqnum  + tx_seqnum_inc;
    if(!data2rtc_stage_is_flow) begin
        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            target[i_f]             <= target_temp[i_f];
        end
        next_target <= target_temp[FPW];
    end
end
end

//Constant propagation, no need for reset condition
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        `ifdef RESET_ALL
        if(!res_n) data2ram_flit[i_f] <= {128{1'b0}};
        else
        `endif
        begin
            data2ram_flit[i_f]      <= data2seq_frp_stage_flit[i_f];

            if(data2seq_frp_stage_flit_is_tail[i_f]) begin
                data2ram_flit[i_f][64+15+3:64+8] <= {tx_seqnum_temp[i_f],tx_frp_adr[target[i_f]],target[i_f]};
            end
        end
    end

    data2ram_flit_is_hdr    <= data2seq_frp_stage_flit_is_hdr | {FPW{data2seq_frp_stage_is_flow}};
    data2ram_flit_is_tail   <= data2seq_frp_stage_flit_is_tail;
    data2ram_flit_is_valid  <= data2seq_frp_stage_flit_is_valid | {FPW{data2seq_frp_stage_is_flow}};
    data2ram_force_tx_retry <= data2seq_frp_stage_force_tx_retry;
if(!res_n) begin
    `ifdef RESET_ALL
        data2ram_flit_is_hdr    <= {FPW{1'b0}};
        data2ram_flit_is_tail   <= {FPW{1'b0}};
        data2ram_flit_is_valid  <= {FPW{1'b0}};
        data2ram_force_tx_retry <= 1'b0;
    `endif

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        tx_frp_adr[i_f]     <= {RAM_ADDR_SIZE{1'b0}};
    end
end else begin

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        if(data2seq_frp_stage_flit_is_valid[i_f]) begin
            tx_frp_adr[target[i_f]] <= tx_frp_adr[target[i_f]] + 1;
        end
    end

end
end

//====================================================================
//---------------------------------Fill RAM
//====================================================================
//-- Always assign FLITs to RAM write register
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif
    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
        ram_w_data[target[i_f]] <= { data2seq_frp_stage_flit_is_valid[i_f],
                                     data2seq_frp_stage_flit_is_tail[i_f],
                                     data2seq_frp_stage_flit_is_hdr[i_f],
                                     data2seq_frp_stage_flit[i_f]
                                  };

        if(data2seq_frp_stage_flit_is_tail[i_f])begin
            ram_w_data[target[i_f]][64+15+3:64+8] <= {tx_seqnum_temp[i_f],tx_frp_adr[target[i_f]],target[i_f]};
        end
    end  

    if(!res_n) begin
        ram_w_en    <= {FPW{1'b0}};
    end else begin
        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            if(data2seq_frp_stage_flit_is_valid[i_f]) begin
                ram_w_en[target[i_f]]    <= 1'b1;
            end else begin
                ram_w_en[target[i_f]]    <= 1'b0;
            end
        end
    end
end

//====================================================================
//---------------------------------Select Data Source: Valid sources are the Retry Buffers or regular data stream.
//====================================================================
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    for(i_f=0;i_f<FPW;i_f=i_f+1)begin
    `ifdef RESET_ALL
    if(!res_n) data2rrp_stage_flit[i_f] <= {128{1'b0}};
    else
    `endif
        begin
            
            if(tx_retry_ongoing) begin
                //-- If there's a TX retry ongoing increment read address until it equals the write address
                data2rrp_stage_flit[i_f]    <= ram_r_data[i_f][127:0];
            end else begin
                //Propagate data from normal packet stream
                data2rrp_stage_flit[i_f]    <= data2ram_flit[i_f];
            end
        end
    end

if(!res_n) begin
    //Reset control signals
    tx_retry_finished   <= 1'b0;
    tx_retry_ongoing    <= 1'b0;
    rf_cnt_retry        <= 1'b0;

    //Ram
    ram_r_en            <= 1'b0;
    ram_r_addr_temp     <= {RAM_ADDR_SIZE{1'b0}};
    ram_r_mask          <= {FPW{1'b0}};

    //Data propagation
    data2rrp_stage_flit_is_hdr      <= {FPW{1'b0}};
    data2rrp_stage_flit_is_tail     <= {FPW{1'b0}};
    data2rrp_stage_flit_is_valid    <= {FPW{1'b0}};

end else begin
    tx_retry_finished   <= 1'b0;
    tx_retry_ongoing    <= 1'b0;
    rf_cnt_retry        <= 1'b0;

    ram_r_en            <= 1'b0;
    ram_r_addr_temp     <= {RAM_ADDR_SIZE{1'b0}};
    ram_r_mask          <= {FPW{1'b0}};

    //if there is a retry request coming set the ram address to last received rrp
    if(data2seq_frp_stage_force_tx_retry) begin
        ram_r_en            <= 1'b1;
        ram_r_addr_temp     <= ram_r_addr+1;
    end

    if(!tx_retry_ongoing) begin

        data2rrp_stage_flit_is_hdr      <= data2ram_flit_is_hdr;
        data2rrp_stage_flit_is_tail     <= data2ram_flit_is_tail;
        data2rrp_stage_flit_is_valid    <= data2ram_flit_is_valid;

        //Switch to retry if requested
        if(data2ram_force_tx_retry) begin

            if(ram_r_addr_temp == ram_w_addr_next) begin //if the next address is the write address -> no retry.
                tx_retry_finished   <= 1'b1;
            end else begin
                ram_r_mask          <= ({FPW{1'b1}}) << (rx_rrp[8-RAM_ADDR_SIZE-1:0]);
                ram_r_addr_temp     <= ram_r_addr_temp+1;
                ram_r_en            <= 1'b1;
                rf_cnt_retry        <= 1'b1;
                tx_retry_ongoing    <= 1'b1;
            end
        end
    end else begin
        //-- If there's a TX retry ongoing increment read addr until it equals the write address

        ram_r_mask          <= {FPW{1'b1}};

        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
                data2rrp_stage_flit_is_hdr[i_f]     <= ram_r_mask[i_f] ? ram_r_data[i_f][128]   :1'b0 ;
                data2rrp_stage_flit_is_tail[i_f]    <= ram_r_mask[i_f] ? ram_r_data[i_f][128+1] :1'b0 ;
                data2rrp_stage_flit_is_valid[i_f]   <= ram_r_mask[i_f] ? ram_r_data[i_f][128+2] :1'b0 ;          
        end    

        //if the next address is the write address -> retry finished
        if(ram_r_addr_temp == ram_w_addr_next) begin
            for(i_f=0;i_f<FPW;i_f=i_f+1)begin
                if(i_f >= target[0] && !(tx_frp_adr[0]==tx_frp_adr[FPW-1]))begin
                    data2rrp_stage_flit_is_hdr[i_f]     <= 1'b0;
                    data2rrp_stage_flit_is_tail[i_f]    <= 1'b0;
                    data2rrp_stage_flit_is_valid[i_f]   <= 1'b0;
                end
            end
            tx_retry_finished   <= 1'b1;
        end else begin
            ram_r_addr_temp     <= ram_r_addr_temp + 1;
            tx_retry_ongoing    <= 1'b1;
            ram_r_en            <= 1'b1;
        end

    end

end
end

//====================================================================
//---------------------------------Add RRP
//====================================================================
`ifdef ASYNC_RES
always @(posedge clk or negedge res_n)  begin `else
always @(posedge clk)  begin `endif

    `ifdef RESET_ALL
        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            data2crc_flit[i_f] <= {128{1'b0}};
        end
    `endif
    begin
        for(i_f=0;i_f<FPW;i_f=i_f+1)begin
            data2crc_flit[i_f]  <= (data2rrp_stage_flit_is_valid[i_f] || !init_state[1]) ? data2rrp_stage_flit[i_f] : {128{1'b0}};

            //Add the RRP
            if(data2rrp_stage_flit_is_tail[i_f] || (data2rrp_stage_flit_is_hdr[i_f] && is_req_flow(data2rrp_stage_flit[i_f])))begin
                data2crc_flit[i_f][64+7:64]     <= rx_hmc_frp;
            end

            //Increment the FRP by 1, It points to the next possible FLIT position -> retry will start there
            if(data2rrp_stage_flit_is_tail[i_f])begin
                data2crc_flit[i_f][64+15:64+8]  <= data2rrp_stage_flit[i_f][64+15:64+8] + 1;
            end

        end
        `ifdef SIMULATION
            if((last_transmitted_rx_hmc_frp != rx_hmc_frp) && !data2rrp_stage_flit_is_valid[0])begin `else 
            if(!data2rrp_stage_flit_is_valid[0] && send_prets)begin `endif
                data2crc_flit[0][63:0]          <= pret_hdr;
                data2crc_flit[0][64+7:64]       <= rx_hmc_frp;
            end
    end

if(!res_n) begin
    `ifdef SIMULATION
        //----Reset control signals
        last_transmitted_rx_hmc_frp <= {8{1'b0}};
    `else 
        send_prets <= 1'b0;
    `endif

    //----Data
    data2crc_flit_is_hdr    <= {FPW{1'b0}};
    data2crc_flit_is_tail   <= {FPW{1'b0}};

end else begin

    //Propagate signals
    data2crc_flit_is_hdr  <= data2rrp_stage_flit_is_hdr;
    data2crc_flit_is_tail <= data2rrp_stage_flit_is_tail |  ((data2rrp_stage_flit_is_hdr[FPW-1] && cmd(data2rrp_stage_flit[FPW-1])==CMD_IRTRY) ? {FPW{1'b1}} : {FPW{1'b0}}) ;

    `ifdef SIMULATION
        //If there is a tail, remember the last transmitted RRP. Otherwise generate PRET if there is a new RRP
        if(|data2rrp_stage_flit_is_tail)begin
            last_transmitted_rx_hmc_frp     <= rx_hmc_frp;
        end 
        if((last_transmitted_rx_hmc_frp != rx_hmc_frp) && !data2rrp_stage_flit_is_valid[0])begin
            data2crc_flit_is_hdr[0]         <= 1'b1;
            data2crc_flit_is_tail[0]        <= 1'b1;
            last_transmitted_rx_hmc_frp     <= rx_hmc_frp;
        end
    `else 

        if(|data2crc_flit_is_hdr) send_prets <= 1'b1;
        if(rf_hmc_sleep_requested || rf_warm_reset) send_prets <= 1'b0;      
        
        if(!data2rrp_stage_flit_is_valid[0] && send_prets)begin
            data2crc_flit_is_hdr[0]         <= 1'b1;
            data2crc_flit_is_tail[0]        <= 1'b1;
        end   
    `endif

end
end

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------INSTANTIATIONS HERE-------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

//Retry Buffer
generate
    for(f=0;f<FPW;f=f+1)begin : retry_buffer_gen
        openhmc_ram #(
            .DATASIZE(128+3),      //FLIT + tail/hdr/valid indicator
            .ADDRSIZE(RAM_ADDR_SIZE)
        )
        retry_buffer_per_lane_I
        (
            .clk(clk),
            .wen(ram_w_en[f]),
            .wdata(ram_w_data[f]),
            .waddr(tx_frp_adr[f]),
            .ren(ram_r_en),
            .raddr(ram_r_addr_temp),
            .rdata(ram_r_data[f])
        );
    end
endgenerate

//HMC CRC Logic
tx_crc_combine #(
    .DWIDTH(DWIDTH),
    .FPW(FPW),
    .LOG_FPW(LOG_FPW)
)
tx_crc_combine_I
(
    .clk(clk),
    .res_n(res_n),
    .d_in_hdr(data2crc_flit_is_hdr),
    .d_in_tail(data2crc_flit_is_tail),
    .d_in_data(data2crc),
    .d_out_data(data_rdy)
);

//Scrambler
generate
    for(n=0;n<NUM_LANES;n=n+1) begin : scrambler_gen
        tx_scrambler #(
            .LANE_WIDTH(LANE_WIDTH),
            .HMC_RX_AC_COUPLED(HMC_RX_AC_COUPLED)
        )
        scrambler_I
        (
            .clk(clk),
            .res_n(res_n),
            .disable_scrambler(rf_scrambler_disable),
            .seed(seed_lane[n]), // unique per lane
            .data_in(data_to_scrambler[n*LANE_WIDTH+LANE_WIDTH-1:n*LANE_WIDTH]),
            .data_out(phy_scrambled_data_out[n*LANE_WIDTH+LANE_WIDTH-1:n*LANE_WIDTH]),
            .rf_run_length_enable(rf_run_length_enable && ~rf_scrambler_disable),
            .rf_run_length_bit_flip(bit_was_flipped[n])
        );
    end
endgenerate

endmodule
`default_nettype wire
