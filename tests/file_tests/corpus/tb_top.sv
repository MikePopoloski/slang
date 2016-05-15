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

`include "axi4_stream_pkg.sv"
`include "hmc_pkg.sv"
`include "hmc_module_pkg.sv"
`include "cag_rgm_rfs_if.sv"



`timescale 100ps/1ps

module tb_top ();

	import uvm_pkg::*;

	//-- include the UVCs
	import axi4_stream_pkg::*;
	import hmc_pkg::*;
	import hmc_module_pkg::*;
	import hmc_base_types_pkg::*;

	`include "cag_rgm.svh"

	`ifdef X16
		`include "register_file_model_16x.sv"
	`else
		`include "register_file_model_8x.sv"
	`endif

	`include "hmc_packet.sv"
	`include "hmc_req_packet.sv"
	`include "hmc_2_axi4_sequencer.sv"
	`include "hmc_2_axi4_sequence.sv"
	`include "tag_handler.sv"
	
	`include "hmc_vseqr.sv"
	
	`include "axi4_stream_hmc_monitor.sv"

	`include "hmc_tb.sv"

	`include "test_lib.sv"

	logic res_n, clk_user, clk_hmc_refclk;

	//-- instantiate the interfaces
	axi4_stream_if #(
		.DATA_BYTES(`AXI4BYTES),
		.TUSER_WIDTH(`AXI4BYTES)
		) axi4_hmc_req_if();

	axi4_stream_if #(
		.DATA_BYTES(`AXI4BYTES),
		.TUSER_WIDTH(`AXI4BYTES)
		) axi4_hmc_rsp_if();

	cag_rgm_rfs_if #(
		.ADDR_WIDTH(`RFS_OPENHMC_RF_AWIDTH),
		.READ_DATA_WIDTH(`RFS_OPENHMC_RF_RWIDTH),
		.WRITE_DATA_WIDTH(`RFS_OPENHMC_RF_WWIDTH)
	) rfs_hmc_if();
	
	hmc_sr_if#(.NUM_LANES(2**`LOG_NUM_LANES)) hmc_if();
	hmc_sr_if#(.NUM_LANES(2**`LOG_NUM_LANES)) hmc_int_if();
	dut dut_I (
		.clk_user(clk_user),
		.clk_hmc_refclk(clk_hmc_refclk),
		.res_n(res_n),
		.hmc(hmc_if),
		.axi4_req(axi4_hmc_req_if),
		.axi4_rsp(axi4_hmc_rsp_if),

		.rfs_hmc(rfs_hmc_if)
		);
	
	assign hmc_int_if.REFCLK_BOOT = hmc_if.REFCLK_BOOT;
	assign hmc_int_if.REFCLKN = hmc_if.REFCLKN;
	assign hmc_int_if.REFCLKP = hmc_if.REFCLKP;
	assign hmc_int_if.P_RST_N = hmc_if.P_RST_N;
	assign hmc_int_if.RXPS = hmc_if.RXPS;
	
	assign hmc_if.TXPS = hmc_int_if.TXPS;
	assign hmc_if.FERR_N = hmc_int_if.FERR_N;
	initial begin

		uvm_config_db#(virtual axi4_stream_if #(.DATA_BYTES(`AXI4BYTES), .TUSER_WIDTH(`AXI4BYTES)))::set(null, "uvm_test_top.hmc_tb0.axi4_req", "vif", axi4_hmc_req_if);
		uvm_config_db#(virtual axi4_stream_if #(.DATA_BYTES(`AXI4BYTES), .TUSER_WIDTH(`AXI4BYTES)))::set(null, "uvm_test_top.hmc_tb0.axi4_rsp", "vif", axi4_hmc_rsp_if);
		
		//hmc_link interfaces
		uvm_config_db#(virtual hmc_sr_if#(.NUM_LANES(2**`LOG_NUM_LANES)))::set(null, "uvm_test_top.hmc_tb0.hmc", "vif", hmc_if);
		uvm_config_db#(virtual hmc_sr_if#(.NUM_LANES(2**`LOG_NUM_LANES)))::set(null, "uvm_test_top.hmc_tb0.hmc", "int_vif", hmc_int_if);
		
		run_test();
	end

	initial begin
		clk_user		<= 1'b1;
		clk_hmc_refclk  <= 1'b1;
		res_n			<= 1'b0;
		#500ns;
		@(posedge clk_user) res_n	<= 1'b1;
	end

	//-- Generate the user clock
	always begin
		case(`FPW)
                2: begin
                    if(`LOG_NUM_LANES==3) //8lanes
                        #1.6ns clk_user = !clk_user;
                    else begin
                    	#0.8ns clk_user = !clk_user;
                    end
                end
                4: begin
                    if(`LOG_NUM_LANES==3) //8lanes
                        #3.2ns clk_user = !clk_user;
                    else
                        #1.6ns clk_user = !clk_user;
                end
                6: begin
                    if(`LOG_NUM_LANES==3) //8lanes
                        #4.8ns clk_user = !clk_user;
                    else
                        #2.4ns clk_user = !clk_user;
                end
                8: begin
                    if(`LOG_NUM_LANES==3) //8lanes
                        #6.4ns clk_user = !clk_user;
                    else
                        #3.2ns clk_user = !clk_user;
                end
            endcase
	end

	//-- 125 MHz HMC/Transceiver refclock
	always #4ns clk_hmc_refclk <= ~clk_hmc_refclk;
	
endmodule : tb_top