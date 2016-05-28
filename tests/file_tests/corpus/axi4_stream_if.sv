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
// AXI4 Stream Interface
//
//

`ifndef AXI4_STREAM_IF_SV
`define AXI4_STREAM_IF_SV

interface axi4_stream_if #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) ();
	
	//--
	//-- Interface signals
	//--

	logic ACLK;    //-- Clock (All signals sampled on the rising edge)
	logic ARESET_N; //-- Global Reset

	logic TVALID;	// Master valid
	logic TREADY;	// Slave ready
	logic [8*DATA_BYTES-1:0] TDATA;	//-- Master data
	logic [TUSER_WIDTH-1:0] TUSER;	//-- Master sideband signals
	
	
	//--
    //--DEBUG signals
    //--
    
	logic [DATA_BYTES/16-1:0] DEBUG_VALIDS;		//-- contains the HMC-VALID Flags
	logic [DATA_BYTES/16-1:0] DEBUG_HEADERS;	//-- contains the HMC-HEADER Flags
	logic [DATA_BYTES/16-1:0] DEBUG_TAILS;		//-- contains the HMC-TAIL Flags
	
	
	//-- assigning the debug signals to TUSER
	assign DEBUG_VALIDS = TUSER[1*(DATA_BYTES /16)-1: (0* DATA_BYTES /16)];
	assign DEBUG_HEADERS = TUSER[2*(DATA_BYTES /16)-1: (1* DATA_BYTES /16)];
	assign DEBUG_TAILS = TUSER[3*(DATA_BYTES /16)-1: (2* DATA_BYTES /16)];
	
	//--
	//-- Interface Coverage
	//--

	covergroup axi4_cg @ (posedge ACLK);
		option.per_instance = 1;
		T_VALID : coverpoint TVALID;
		T_READY : coverpoint TREADY;

		//-- cover the amount of consecutive AXI4 transactions
		CONSECUTIVE_TRANSACTIONS: coverpoint {TVALID , TREADY}{
			bins transactions_single	= (0,1,2 =>3			=> 0,1,2);
			bins transactions_1_5[] 	= (0,1,2 =>3[*2:10] 	=> 0,1,2);
			bins transactions_11_50[] 	= (0,1,2 =>3[*11:50]	=> 0,1,2);
			bins transactions_huge 		= (0,1,2 =>3[*51:100000]=> 0,1,2);
		}

		//-- cover the waiting time after TVALID is set until TREADY in clock cycles
		TRANSACTION_WAITING: coverpoint {TVALID , TREADY}{
			bins zero_waiting_time		= (0,1				=> 3);
			bins low_waiting_time[]		= (2[*1:5]			=> 3);
			bins medium_waiting_time[]	= (2[*6:15] 		=> 3);
			bins high_waiting_time		= (2[*16:100000] 	=> 3);
			illegal_bins illegal		= (2				=> 0);
		}
		
		//-- Pause between Transactions
		TRANSACTION_PAUSE: coverpoint {TVALID , TREADY}{
			bins low_waiting_time[]		= (3 => 0[*1:5]		=> 2,3);
			bins medium_waiting_time[]	= (3 => 0[*6:15] 	=> 2,3);
			bins high_waiting_time		= (3 => 0[*16:100] 	=> 2,3);
		}
		
		//-- cover the time TREADY is active until deassertion or TVALID in clock cycles
		READY_WITHOUT_VALID: coverpoint {TVALID , TREADY}{
			bins short_ready_time[]		= (1[*1:5]  	=> 3,0);
			bins medium_ready_time[]	= (1[*6:15] 	=> 3,0);
			bins high_ready_time		= (1[*16:100000]=> 3,0);
		}

		//--cover all available transitions of TVALID/TREADY
		CASES_VALID_READY : cross T_VALID, T_READY;
		TRANSITIONS: coverpoint {TVALID, TREADY}{
			bins transition[] = ( 0,1,3 => [0:3]), (2 => 2,3) ;
		}

		//-- cover active VALID Flags
		VALID_FLAGS : coverpoint DEBUG_VALIDS;

		VALID_TRANSITIONS : coverpoint DEBUG_VALIDS {
			bins transition [] = ( [1:(1<<($size(DEBUG_VALIDS))) -1] => [1:(1<<($size(DEBUG_VALIDS))) -1] );
		}

		//-- cover active HEADER Flags
		HDR_FLAGS   : coverpoint DEBUG_HEADERS;
		
		HDR_TRANSITIONS : coverpoint DEBUG_HEADERS {
			bins transition [] = ( [1:1<<($size(DEBUG_HEADERS)) -1] => [1:1<<($size(DEBUG_HEADERS)) -1] );
		}

		//-- cover active TAIL Flags
		TAIL_FLAGS  : coverpoint DEBUG_TAILS;

		TAIL_TRANSITIONS : coverpoint DEBUG_TAILS {
			bins transition [] = ( [1:1<<($size(DEBUG_TAILS)) -1] => [1:1<<($size(DEBUG_TAILS)) -1] );
		}

		CROSS_HDR_TAILS : cross HDR_FLAGS, TAIL_FLAGS;
		
		HDR_TAILS : coverpoint { DEBUG_HEADERS != {$size(DEBUG_HEADERS){1'b0}} ,DEBUG_TAILS != {$size(DEBUG_TAILS){1'b0}}   };
		
		

	endgroup

	//-- creating an instance of the covergroup
	axi4_cg axi4 = new();



	//--
	//-- Interface Assertions
	//--


	//property reset_synchronous_deassert_p;
	//	@(edge ACLK)
	//	!ARESET_N |-> ARESET_N[->1];
	//
	//endproperty

	// chk_reset_tvalid	: assert property (
	// 	//-- TVALID must be inactive during Reset
	// 	@(posedge ACLK)
	// 	!ARESET_N |-> TVALID == 1'b0
	// );


	chk_valid_hold 		: assert property (
		//-- if TVALID is set it must be active until TREADY
		@(posedge ACLK) disable iff(!ARESET_N)
		(TVALID == 1 && TREADY == 0) |=> (TVALID==1)
	);


	chk_valid_headers 	: assert property (
		//-- check if HEADER Flags are a subset of VALID Flags
		@(posedge ACLK) disable iff (!ARESET_N)
		(TVALID == 1'b1)    |-> (DEBUG_VALIDS | DEBUG_HEADERS
							  == DEBUG_VALIDS)
	);


	chk_valid_tails 	: assert property (
		//-- check if TAIL Flags are a subset of VALID Flags
		@(posedge ACLK) disable iff (!ARESET_N)
		(TVALID == 1'b1)    |-> (DEBUG_VALIDS | DEBUG_TAILS
							  == DEBUG_VALIDS)
	);


	check_spanning_hmc_pkts	: assert property (
		//-- check that TVALID stays high if a hmc_packet ranges over multiple axi cycles
		//-- starts if more header than tails
		//-- completes if more tails than header
		@(posedge ACLK  )  disable iff (!ARESET_N)
			(TVALID &&						( $countones(DEBUG_HEADERS) > $countones(DEBUG_TAILS) ))
			|=>	(TVALID == 1) throughout 	( $countones(DEBUG_HEADERS) < $countones(DEBUG_TAILS) )[->1]
	);

	time clk_rise;
	time reset_rise;

	always @(posedge ACLK) begin	
		if(ARESET_N == 0)
			clk_rise <= $time();
	end
	
	always @(posedge ARESET_N) begin
		reset_rise <= $time();
	end
	
	//TODO TODO ADD
	// check_sync_reset : assert property (
	// 	@(posedge ACLK)
	// 	$rose(ARESET_N) |=> (reset_rise == clk_rise)
	// 	);

	property data_hold_p;
		//-- if TVALID is set TDATA must not be changed until TREADY
		logic [8*DATA_BYTES-1:0] m_data;

		@(posedge ACLK) disable iff(!ARESET_N)
			(TVALID == 1 && TREADY == 0,m_data = TDATA) |=> (TDATA == m_data);
	endproperty : data_hold_p

	property user_hold_p;
		//-- if TVALID is set TUSER must not be changed until TREADY
		logic [TUSER_WIDTH-1:0] m_user;

		@(posedge ACLK) disable iff(!ARESET_N)
			(TVALID == 1 && TREADY == 0,m_user = TUSER) |=> (TUSER == m_user);
	endproperty : user_hold_p

	chk_data_hold 		: assert property(   data_hold_p);
	chk_user_hold		: assert property(   user_hold_p);



endinterface : axi4_stream_if

`endif // AXI4_STREAM_IF_SV

