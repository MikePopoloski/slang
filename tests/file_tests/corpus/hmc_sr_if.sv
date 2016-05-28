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
//
//
// Short Range Hybrid Memory Cube Interface
//
//

`ifndef HMC_SR_IF_SV
`define HMC_SR_IF_SV

interface hmc_sr_if #(parameter NUM_LANES = 16) ();

	//--
	//-- interface signals
	//--
	
	logic REFCLKP; // Link Reference clock
	logic REFCLKN;

	logic [1:0] REFCLK_BOOT; // 00 -> 125 MHz, 01 -> 156.25 MHz, 10 -> 166.67 MHz

	logic P_RST_N; 

	//-- Differential pairs
	logic [NUM_LANES - 1 : 0]	RXP;
	logic [NUM_LANES - 1 : 0]	RXN;

	logic [NUM_LANES - 1 : 0]	TXP;
	logic [NUM_LANES - 1 : 0]	TXN;

	logic RXPS; // Power-reduction input
	logic TXPS; // Power-reduction output

	logic FERR_N; // Fatal error indicator
	
	//--
	//-- Checking & Coverage
	//--
	
	time t_IS 	= 10ns;	//-- see the Spec
	time t_RST 	= 20ns;	//-- minimum reset time
	
	time t_PST = 80ns;
	time t_SS =  525ns; //-- since revision E
	time t_SME = 600ns;
	time t_SREF = 1us;//-- should be 1ms in the real system 
	
	time reset_fall = 0;
	time RXPS_rise;
	time TXPS_rise;
	time reset_rise;
	
	time RXPS_fall;
	time TXPS_fall = 0;
	
	
	bit txp_z = 0;
	event wakeup;
	event sleep;
	
	covergroup rst_times_cg @ (posedge P_RST_N);
		option.per_instance = 1;
		RXPS_rise_BEFORE_P_RST_N : coverpoint $time() - RXPS_rise {
			bins small_time[100] = {[1*t_IS+1:100*t_IS-1]};
			bins huge_time = {[100*t_IS:$]};
			illegal_bins illegal = {[0:t_IS]};
		}
		P_RST_N_length : coverpoint $time() - reset_fall {
			bins small_time[100] = {[1*t_RST+1:100*t_RST-1]};
			bins huge_time = {[100*t_RST:$]};
			illegal_bins illegal = {[0:t_RST]};
		} 
	endgroup
	
	
	
	covergroup sleep_times_cg @ (posedge RXPS);
		option.per_instance = 1;
		SLEEP_TIME	: coverpoint $time - RXPS_fall {
			bins short_sleep[20] = {[2*t_SREF:20*t_SREF]};
			bins long_sleep = {[21*t_SREF:$]};
			illegal_bins illegal = {[0:t_SREF-1]};
		}
	endgroup
	
	
	covergroup prepare_sleep_cg @ (sleep);
		option.per_instance = 1;
		PREPARE_SLEEP_TIME : coverpoint TXPS_fall - RXPS_fall {
			bins short_sleep		= {[0				:t_PST]};
			bins waiting_t_sme[3]	= {[t_PST			:3*t_SS]};
			illegal_bins illegal	= {[t_PST+ 3*t_SS+1:$]};
		}
		SWITCH_TO_Z : coverpoint $time - TXPS_fall {
			bins short = {[0:t_SME/2]};
			bins long = {[t_SME/2 + 1: t_SME]};
			illegal_bins illegal = {[t_SME+1:$]};
		}
	endgroup
	
	
	covergroup prepare_wakeup_cg @ (wakeup);
		option.per_instance = 1;
		PREPARE_WAKEUP_TIME : coverpoint TXPS_rise - RXPS_rise {
			bins short_sleep		= {[0				:t_PST]};
			bins waiting_t_sme[3]	= {[t_PST			:3*t_SS]};
			illegal_bins illegal	= {[t_PST+ 3*t_SS+1:$]};
		}
		SWITCH_FROM_Z : coverpoint $time - TXPS_rise {
			bins short = {[0:t_SME/2]};
			bins long = {[t_SME/2 + 1: t_SME]};
			illegal_bins illegal = {[t_SME+1:$]};
		}
		
	endgroup
	
	
	rst_times_cg rst_times = new();
	sleep_times_cg sleep_times = new();
	prepare_sleep_cg prepare_sleep = new();
	prepare_wakeup_cg prepare_wakeup = new();
	
	//always @(posedge RXPS) begin	
	//	if(P_RST_N == 0)
	//		RXPS_rise <= $time();
	//end
	
	always @(posedge P_RST_N) begin
		reset_rise <= $time();
	end
	
	always @(negedge P_RST_N) begin
		reset_fall <= $time();
	end
	
	always @(negedge RXPS) begin	
			RXPS_fall <= $time();
	end
	always @(negedge TXPS) begin	
			TXPS_fall = $time();
			//->sleep;
	end
	
	always @(TXP) begin
		if (TXP === {NUM_LANES{1'bz}})begin
			->sleep;
			txp_z = 1;
		end
		else begin
			if (RXPS_rise >0) begin
				if (txp_z == 1)begin
					->wakeup;
				end
				txp_z = 0;
			end
		end
	end

	always @(posedge RXPS) begin	
			RXPS_rise <= $time();
	end
	always @(posedge TXPS) begin	
			TXPS_rise = $time();
	end

	//-- reset checks
	chk_RXPS_before_P_RST_N : assert property (
		@(posedge REFCLKP)
		$rose(P_RST_N) |=> (reset_rise >= RXPS_rise + t_IS)
		);
		
	chk_P_RST_N_length : assert property (
		@(posedge REFCLKP)
		$rose(P_RST_N) |=> (t_RST <= reset_rise - reset_fall)
		);	
		
		
	chk_Lanes_HIGH_Z_during_P_RST_N_P : assert property (
		@(posedge REFCLKP)
			!P_RST_N |-> (TXP === { NUM_LANES{1'bZ}})
		);
	chk_Lanes_HIGH_Z_during_P_RST_N_N : assert property (
		@(posedge REFCLKP)
			!P_RST_N |-> (TXN === { NUM_LANES{1'bZ}})
		);
	
	
	
	//-- sleep mode checks --//
	
	//-- txps falling edge within t_PST + 3* t_SME after rxps falling edge
	chk_TXPS_fall_after_RXPS : assert property (
		@(posedge REFCLKP)
			$fell(TXPS) |->(t_PST+ 3* t_SME >= TXPS_fall - RXPS_fall)
		);
	
	chk_TXPS_rise_after_RXPS : assert property (
		@(posedge REFCLKP)
			$rose(TXPS) |->((t_PST+ 3* t_SME >= TXPS_rise - RXPS_rise)|| RXPS_rise <= reset_rise)
		);

		chk_sleep_mode_min_duration : assert property (
		@(posedge REFCLKP) disable iff (!P_RST_N)
			$rose(RXPS)  |->(t_SREF <= RXPS_rise - RXPS_fall)
		);

endinterface : hmc_sr_if

`endif // HMC_SR_IF_SV

