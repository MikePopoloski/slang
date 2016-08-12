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

`ifndef HMC_LINK_CONFIG_SV
`define HMC_LINK_CONFIG_SV

class hmc_link_config extends uvm_object;

//-- 
//-- variables
//-- 

	rand int 			hmc_tokens;
	rand int 			rx_tokens;
	rand bit [5:0]		bit_slip_time;
	rand bit [2:0]  	cube_id;

	rand bit 			cfg_tx_lane_reverse;
	rand bit [15:0] 	cfg_hsstx_inv;
	bit 			cfg_scram_enb = 1;
	rand bit [15:0]		cfg_tx_lane_delay[16];
	rand bit [ 3:0]		cfg_retry_limit			= 3;	//-- LINKRETRY - infinite retry when cfg_retry_limit[3] == 1
	rand bit [ 2:0]		cfg_retry_timeout		= 5;

	rand bit			cfg_check_pkt			= 1;	//-- check for valid packet

	bit 				cfg_lane_auto_correct 	= 1;
	uvm_active_passive_enum 				cfg_rsp_open_loop = UVM_PASSIVE;
	bit 				cfg_half_link_mode_rx 	= (`LOG_NUM_LANES==3);
	bit [7:0] 			cfg_tx_rl_lim 			= 85;
	`ifdef HMC_12G
	int 				cfg_rx_clk_ratio 		= 50;	//Set to 50 for 12.5Gbit , 60 for 15Gbit
	int 				cfg_tx_clk_ratio 		= 50;	//Set to 50 for 12.5Gbit , 60 for 15Gbit
	`else 
	int 				cfg_rx_clk_ratio 		= 40;	//Set to 50 for 12.5Gbit , 60 for 15Gbit
	int 				cfg_tx_clk_ratio 		= 40;	//Set to 50 for 12.5Gbit , 60 for 15Gbit
	`endif
	bit 				cfg_half_link_mode_tx	= (`LOG_NUM_LANES==3);
	rand bit [7:0]		cfg_init_retry_rxcnt;
	rand bit [7:0]		cfg_init_retry_txcnt;	//-- Actual value in BFM is 4times this value
	realtime 			cfg_tsref				= 1us;
	realtime 			cfg_top					= 1us;

	bit 				cfg_retry_enb			= 1;

	//-- error injection is defined in 0.1% granularity
    rand int unsigned	cfg_rsp_dln,	cfg_rsp_lng,		cfg_rsp_crc,	cfg_rsp_seq,
						cfg_rsp_dinv,	cfg_rsp_errstat,	cfg_rsp_err,	cfg_rsp_poison,
						cfg_req_dln,	cfg_req_lng,		cfg_req_crc,	cfg_req_seq;

//--
//-- constrains
//--

	constraint cfg_init_retry_rxcnt_c {
		cfg_init_retry_rxcnt == 16;
		// cfg_init_retry_rxcnt <= 20;
	}

	constraint cfg_init_retry_txcnt_c {
		//Actual Value is constraint*4
		// cfg_init_retry_txcnt >= 5;	
		cfg_init_retry_txcnt == 7;
	}

	constraint bit_slip_time_c {
		bit_slip_time >= 32;
		bit_slip_time <= 63;
	}

	constraint hmc_tokens_c {
		hmc_tokens >= 25;
		// soft hmc_tokens dist{[25:30]:/5, [31:100]:/15, [101:1023]:/80}; 
		soft hmc_tokens dist{[25:30]:/5, [31:219]:/95};	//Current hardware
	}

	constraint cfg_hsstx_inv_c {
		cfg_hsstx_inv >= 0;
	}

	constraint rx_tokens_c {
		rx_tokens >= 9;
		// soft rx_tokens dist{[9:30]:/5, [31:100]:/15, [101:1023]:/80}; 	//Make sure to increase the input buffer accordingly 
		soft rx_tokens dist{[9:30]:/5, [31:255]:/95};	//Safe value for input buffer address size = 8. Leave some FLITs for poisoned packets
	}

	constraint cube_id_c {
		cube_id >= 0;
		soft cube_id == 0; 
	}
	constraint lane_delay_c{
		foreach (cfg_tx_lane_delay[i]) {
			cfg_tx_lane_delay[i] >=	0;
			cfg_tx_lane_delay[i] <= 8;
		}
	}

	constraint retry_timeout_c {
		cfg_retry_timeout == 7;
	}


	constraint error_rates_c {
		soft cfg_rsp_dln	==0;//dist{[0:10]};
		soft cfg_rsp_lng	==0;//dist{[0:10]};
		soft cfg_rsp_crc	==0;//dist{[0:10]};
		soft cfg_rsp_seq	==0;//dist{[0:10]};
		soft cfg_rsp_poison	==0;//dist{[0:10]}; 
		soft cfg_req_dln 	==0;//dist{[0:10]};
		soft cfg_req_lng 	==0;//dist{[0:10]};
		soft cfg_req_crc 	==0;//dist{[0:10]};
		soft cfg_req_seq 	==0; // Must be zero for BFM 28965 !

        (
        cfg_rsp_dln          ||
        cfg_rsp_lng          ||
        cfg_rsp_crc          ||
        cfg_rsp_seq          ||
        cfg_rsp_dinv         ||
        cfg_rsp_errstat      ||
        cfg_rsp_err          ||
        cfg_rsp_poison       ||

        cfg_req_dln          ||
        cfg_req_lng          ||
        cfg_req_crc          ||
        cfg_req_seq
        ) -> {
            cfg_check_pkt      == 0; //-- disable packet checking
            cfg_retry_limit[3] == 1; //-- enable infinite retry
        }
	}


	`uvm_object_utils_begin(hmc_link_config)
		`uvm_field_int(hmc_tokens, UVM_DEFAULT)
		`uvm_field_int(rx_tokens, UVM_DEFAULT)
	`uvm_object_utils_end

	function new(string name = "hmc_link_config");
		super.new(name);
	endfunction : new

	virtual function void do_print (uvm_printer printer);
		super.do_print(printer);
	endfunction : do_print

endclass : hmc_link_config

`endif // HMC_LINK_CONFIG_SV
