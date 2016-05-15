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
 *  Module name: openhmc_rf
 *
 */

`default_nettype none

module openhmc_rf #(
    parameter NUM_LANES         = 8,
    parameter XIL_CNT_PIPELINED = 1,
    parameter LOG_MAX_RX_TOKENS = 8,
    parameter LOG_MAX_HMC_TOKENS= 8,
    parameter RF_COUNTER_SIZE   = 64,
    parameter HMC_RF_RWIDTH     = 0,
    parameter HMC_RF_AWIDTH     = 0,
    parameter HMC_RF_WWIDTH     = 0
) (
    input wire clk,
    input wire res_n,
    input wire [HMC_RF_AWIDTH-1:0] address,
    output reg invalid_address,
    output reg access_complete,
    input wire read_en,
    output reg[HMC_RF_RWIDTH-1:0] read_data,
    input wire write_en,
    input wire[HMC_RF_WWIDTH-1:0] write_data,
    input wire status_general_link_up_next,
    input wire status_general_link_training_next,
    input wire status_general_sleep_mode_next,
    input wire status_general_FERR_N_next,
    input wire status_general_lanes_reversed_next,
    input wire status_general_phy_tx_ready_next,
    input wire status_general_phy_rx_ready_next,
    input wire[LOG_MAX_HMC_TOKENS-1:0] status_general_hmc_tokens_remaining_next,
    input wire[LOG_MAX_RX_TOKENS-1:0] status_general_rx_tokens_remaining_next,
    input wire[NUM_LANES-1:0] status_general_lane_polarity_reversed_next,
    input wire[NUM_LANES-1:0] status_init_lane_descramblers_locked_next,
    input wire[NUM_LANES-1:0] status_init_descrambler_part_aligned_next,
    input wire[NUM_LANES-1:0] status_init_descrambler_aligned_next,
    input wire status_init_all_descramblers_aligned_next,
    input wire[2:0] status_init_rx_init_state_next,
    input wire[1:0] status_init_tx_init_state_next,
    output reg control_p_rst_n,
    output reg control_hmc_init_cont_set,
    output reg control_set_hmc_sleep,
    output reg control_warm_reset,
    output reg control_scrambler_disable,
    output reg control_run_length_enable,
    output reg[LOG_MAX_RX_TOKENS-1:0] control_rx_token_count,
    output reg[4:0] control_irtry_received_threshold,
    output reg[4:0] control_irtry_to_send,
    input wire[RF_COUNTER_SIZE-1:0] sent_p_cnt_next,
    input wire[RF_COUNTER_SIZE-1:0] sent_np_cnt_next,
    input wire[RF_COUNTER_SIZE-1:0] sent_r_cnt_next,
    input wire[RF_COUNTER_SIZE-1:0] poisoned_packets_cnt_next,
    input wire[RF_COUNTER_SIZE-1:0] rcvd_rsp_cnt_next,
    input wire tx_link_retries_count_countup,
    input wire errors_on_rx_count_countup,
    input wire run_length_bit_flip_count_countup,
    input wire error_abort_not_cleared_count_countup
);
    reg status_general_link_up;
    reg status_general_link_training;
    reg status_general_sleep_mode;
    reg status_general_FERR_N;
    reg status_general_lanes_reversed;
    reg status_general_phy_tx_ready;
    reg status_general_phy_rx_ready;
    reg[LOG_MAX_HMC_TOKENS-1:0] status_general_hmc_tokens_remaining;
    reg[LOG_MAX_RX_TOKENS-1:0] status_general_rx_tokens_remaining;
    reg[NUM_LANES-1:0] status_general_lane_polarity_reversed;
    reg[NUM_LANES-1:0] status_init_lane_descramblers_locked;
    reg[NUM_LANES-1:0] status_init_descrambler_part_aligned;
    reg[NUM_LANES-1:0] status_init_descrambler_aligned;
    reg status_init_all_descramblers_aligned;
    reg[2:0] status_init_rx_init_state;
    reg[1:0] status_init_tx_init_state;
    reg[RF_COUNTER_SIZE-1:0] sent_p_cnt;
    reg[RF_COUNTER_SIZE-1:0] sent_np_cnt;
    reg[RF_COUNTER_SIZE-1:0] sent_r_cnt;
    reg[RF_COUNTER_SIZE-1:0] poisoned_packets_cnt;
    reg[RF_COUNTER_SIZE-1:0] rcvd_rsp_cnt;
    reg rreinit;
    wire[47:0] tx_link_retries_count;
    wire[47:0] errors_on_rx_count;
    wire[47:0] run_length_bit_flip_count;
    wire[47:0] error_abort_not_cleared_count;
    
    `ifdef XILINX
        openhmc_counter48_wrapper_xilinx #(
            .INC_SIZE(1),
            .PIPELINED(XIL_CNT_PIPELINED)
        ) tx_link_retries_count_I (
            .clk(clk),
            .res_n(res_n),
            .inc_value(tx_link_retries_count_countup),
            .value(tx_link_retries_count)
        );
        
        openhmc_counter48_wrapper_xilinx #(
            .INC_SIZE(1),
            .PIPELINED(XIL_CNT_PIPELINED)
        ) errors_on_rx_count_I (
            .clk(clk),
            .res_n(res_n),
            .inc_value(errors_on_rx_count_countup),
            .value(errors_on_rx_count)
        );
        
        openhmc_counter48_wrapper_xilinx #(
            .INC_SIZE(1),
            .PIPELINED(XIL_CNT_PIPELINED)
        ) run_length_bit_flip_count_I (
            .clk(clk),
            .res_n(res_n),
            .inc_value(run_length_bit_flip_count_countup),
            .value(run_length_bit_flip_count)
        );
        
        openhmc_counter48_wrapper_xilinx #(
            .INC_SIZE(1),
            .PIPELINED(XIL_CNT_PIPELINED)
        ) error_abort_not_cleared_count_I (
            .clk(clk),
            .res_n(res_n),
            .inc_value(error_abort_not_cleared_count_countup),
            .value(error_abort_not_cleared_count)
        );    
    `else 
        openhmc_counter48 #(
        	.DATASIZE(48)
        ) tx_link_retries_count_I (
        	.clk(clk),
        	.res_n(res_n),
        	.increment(tx_link_retries_count_countup),
        	.load_enable(rreinit),
        	.value(tx_link_retries_count)
        );
        
        openhmc_counter48 #(
        	.DATASIZE(48)
        ) errors_on_rx_count_I (
        	.clk(clk),
        	.res_n(res_n),
        	.increment(errors_on_rx_count_countup),
        	.load_enable(rreinit),
        	.value(errors_on_rx_count)
        );
        
        openhmc_counter48 #(
        	.DATASIZE(48)
        ) run_length_bit_flip_count_I (
        	.clk(clk),
        	.res_n(res_n),
        	.increment(run_length_bit_flip_count_countup),
        	.load_enable(rreinit),
        	.value(run_length_bit_flip_count)
        );
        
        openhmc_counter48 #(
        	.DATASIZE(48)
        ) error_abort_not_cleared_count_I (
        	.clk(clk),
        	.res_n(res_n),
        	.increment(error_abort_not_cleared_count_countup),
        	.load_enable(rreinit),
        	.value(error_abort_not_cleared_count)
        );
    `endif
    
    //Register: status_general
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            status_general_link_up          <= 1'h0;
            status_general_link_training    <= 1'h0;
            status_general_sleep_mode       <= 1'h0;
            status_general_FERR_N           <= 1'h0;
            status_general_lanes_reversed   <= 1'h0;
            status_general_phy_tx_ready     <= 1'h0;
            status_general_phy_rx_ready     <= 1'h0;
            status_general_hmc_tokens_remaining     <= {LOG_MAX_HMC_TOKENS{1'b0}};
            status_general_rx_tokens_remaining      <= {LOG_MAX_RX_TOKENS{1'b0}};
            status_general_lane_polarity_reversed   <= {NUM_LANES{1'b0}};
        end
        else
        `endif
        begin
            status_general_link_up      <= status_general_link_up_next;
            status_general_link_training<= status_general_link_training_next;
            status_general_sleep_mode   <= status_general_sleep_mode_next;
            status_general_FERR_N       <= status_general_FERR_N_next;
            status_general_lanes_reversed   <= status_general_lanes_reversed_next;
            status_general_phy_tx_ready     <= status_general_phy_tx_ready_next;
            status_general_phy_rx_ready     <= status_general_phy_rx_ready_next;
            status_general_hmc_tokens_remaining     <= status_general_hmc_tokens_remaining_next;
            status_general_rx_tokens_remaining      <= status_general_rx_tokens_remaining_next;
            status_general_lane_polarity_reversed   <= status_general_lane_polarity_reversed_next;
        end

    end
    
    //Register: status_init
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            status_init_lane_descramblers_locked<= {NUM_LANES{1'b0}};
            status_init_descrambler_part_aligned<= {NUM_LANES{1'b0}};
            status_init_descrambler_aligned     <= {NUM_LANES{1'b0}};
            status_init_all_descramblers_aligned<= 1'h0;
            status_init_rx_init_state           <= 3'h0;
            status_init_tx_init_state           <= 2'h0;
        end
        else
        `endif
        begin
            status_init_lane_descramblers_locked<= status_init_lane_descramblers_locked_next;
            status_init_descrambler_part_aligned<= status_init_descrambler_part_aligned_next;
            status_init_descrambler_aligned     <= status_init_descrambler_aligned_next;
            status_init_all_descramblers_aligned<= status_init_all_descramblers_aligned_next;
            status_init_rx_init_state           <= status_init_rx_init_state_next;
            status_init_tx_init_state           <= status_init_tx_init_state_next;
        end

    end
    
    //Register: control
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
     
        if(!res_n)
        begin
            control_p_rst_n             <= 1'h0;
            control_hmc_init_cont_set   <= 1'b0;
            control_set_hmc_sleep       <= 1'h0;
            control_warm_reset          <= 1'h0;
            control_scrambler_disable   <= 1'h0;
            control_run_length_enable   <= 1'h0;
            control_rx_token_count      <= {LOG_MAX_RX_TOKENS{1'b1}};
            control_irtry_received_threshold    <= 5'h10;
            control_irtry_to_send       <= 5'h18;
        end
        else
        begin
            
            if((address == 2) && write_en)
            begin
                control_p_rst_n <= write_data[0:0];
            end
            
            if((address == 2) && write_en)
            begin
                control_hmc_init_cont_set <= write_data[1:1];
            end
            
            if((address == 2) && write_en)
            begin
                control_set_hmc_sleep <= write_data[2:2];
            end
            
            if((address == 2) && write_en)
            begin
                control_warm_reset <= write_data[3:3];
            end
            
            if((address == 2) && write_en)
            begin
                control_scrambler_disable <= write_data[4:4];
            end
            
            if((address == 2) && write_en)
            begin
                control_run_length_enable <= write_data[5:5];
            end
            
            if((address == 2) && write_en)
            begin
                control_rx_token_count <= write_data[16+LOG_MAX_RX_TOKENS-1:16];
            end
            
            if((address == 2) && write_en)
            begin
                control_irtry_received_threshold <= write_data[36:32];
            end
            
            if((address == 2) && write_en)
            begin
                control_irtry_to_send <= write_data[44:40];
            end
            
        end

    end
    
    //Register: sent_p
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL       
        if(!res_n)
        begin
            sent_p_cnt <= {RF_COUNTER_SIZE{1'b0}};
        end
        else
        `endif
        begin
            sent_p_cnt <= sent_p_cnt_next;
        end

    end
    
    //Register: sent_np
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            sent_np_cnt <= {RF_COUNTER_SIZE{1'b0}};
        end
        else
        `endif
        begin
            sent_np_cnt <= sent_np_cnt_next;
        end

    end
    
    //Register: sent_r
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            sent_r_cnt <= {RF_COUNTER_SIZE{1'b0}};
        end
        else
        `endif
        begin
            sent_r_cnt <= sent_r_cnt_next;
        end

    end
    
    //Register: poisoned_packets
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            poisoned_packets_cnt <= {RF_COUNTER_SIZE{1'b0}};
        end
        else
        `endif
        begin
            poisoned_packets_cnt <= poisoned_packets_cnt_next;
        end

    end
    
    //Register: rcvd_rsp
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
        `ifdef RESET_ALL        
        if(!res_n)
        begin
            rcvd_rsp_cnt <= {RF_COUNTER_SIZE{1'b0}};
        end
        else
        `endif
        begin
            rcvd_rsp_cnt <= rcvd_rsp_cnt_next;
        end

    end
    
    //Register: counter_reset
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
                
        if(!res_n)
        begin
            rreinit <= 1'b0;
        end
        else
        begin
            
            if((address == 8) && write_en)
            begin
                rreinit <= 1'b1;
            end
            else
            begin
                rreinit <= 1'b0;
            end
        end

    end
    
    //Address Decoder Software Read:
    `ifdef ASYNC_RES
    always @(posedge clk or negedge res_n) `else
    always @(posedge clk) `endif
    begin
                
        if(!res_n)
        begin
            invalid_address <= 1'b0;
            access_complete <= 1'b0;
            read_data       <= {HMC_RF_RWIDTH{1'b0}};
        end
        else
        begin
            
            casex(address)
                4'h0:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[0:0] <= status_general_link_up;
                    read_data[1:1] <= status_general_link_training;
                    read_data[2:2] <= status_general_sleep_mode;
                    read_data[3:3] <= status_general_FERR_N;
                    read_data[4:4] <= status_general_lanes_reversed;
                    read_data[8:8] <= status_general_phy_tx_ready;
                    read_data[9:9] <= status_general_phy_rx_ready;
                    read_data[16+LOG_MAX_HMC_TOKENS-1:16] <= status_general_hmc_tokens_remaining;
                    read_data[32+LOG_MAX_RX_TOKENS-1:32] <= status_general_rx_tokens_remaining;
                    read_data[63:48] <= status_general_lane_polarity_reversed;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h1:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[NUM_LANES-1:0] <= status_init_lane_descramblers_locked;
                    read_data[16+NUM_LANES-1:16] <= status_init_descrambler_part_aligned;
                    read_data[32+NUM_LANES-1:32] <= status_init_descrambler_aligned;
                    read_data[48:48] <= status_init_all_descramblers_aligned;
                    read_data[51:49] <= status_init_rx_init_state;
                    read_data[53:52] <= status_init_tx_init_state;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h2:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[0:0] <= control_p_rst_n;
                    read_data[1:1] <= control_hmc_init_cont_set;
                    read_data[2:2] <= control_set_hmc_sleep;
                    read_data[3:3] <= control_warm_reset;
                    read_data[4:4] <= control_scrambler_disable;
                    read_data[5:5] <= control_run_length_enable;
                    read_data[16+LOG_MAX_RX_TOKENS-1:16] <= control_rx_token_count;
                    read_data[36:32] <= control_irtry_received_threshold;
                    read_data[44:40] <= control_irtry_to_send;
                    invalid_address <= 1'b0;
                    access_complete <= read_en || write_en;
                end
                4'h3:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[RF_COUNTER_SIZE-1:0] <= sent_p_cnt;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h4:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[RF_COUNTER_SIZE-1:0] <= sent_np_cnt;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h5:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[RF_COUNTER_SIZE-1:0] <= sent_r_cnt;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h6:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[RF_COUNTER_SIZE-1:0] <= poisoned_packets_cnt;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h7:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[RF_COUNTER_SIZE-1:0] <= rcvd_rsp_cnt;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'h8:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    invalid_address <= read_en;
                    access_complete <= read_en || write_en;
                end
                4'h9:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[47:0] <= tx_link_retries_count;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'ha:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[47:0] <= errors_on_rx_count;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'hb:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[47:0] <= run_length_bit_flip_count;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                4'hc:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    read_data[47:0] <= error_abort_not_cleared_count;
                    invalid_address <= write_en;
                    access_complete <= read_en || write_en;
                end
                default:
                begin
                    read_data       <= {HMC_RF_RWIDTH{1'b0}};
                    invalid_address <= read_en || write_en;
                    access_complete <= read_en || write_en;
                end

            endcase
        end

    end

endmodule

`default_nettype wire
