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
`ifndef hmc_config_SV
`define hmc_config_SV




class hmc_local_link_config extends uvm_object;
	// Configure the driver
	rand bit [15:0] reverse_polarity;
	rand bit		reverse_lanes;
	rand int		TS1_Messages;

	rand int		irtry_flit_count_to_send;
	rand int		irtry_flit_count_received_threshold;

	int				random_retry_probability;
	rand int		max_retry_attempts;
	
	rand int		lane_delays[16];
	rand bit		lane_delays_enabled=1;

	bit 			errors_enabled 		= 0;
	bit 			lane_errors_enabled	= 0;
	rand int		poisoned_probability; 
	rand int		lng_error_probability;
	rand int		seq_error_probability;
	rand int		crc_error_probability;
	rand int		bitflip_error_probability;
	
	rand int		poisoned_packets_minimum_length;
	uvm_active_passive_enum	active = UVM_PASSIVE;
	int				width;

	rand int		send_tret_time;
	rand int		send_pret_time;
	
	bit requester = 1'b1;
	int run_length_limit = 85;

	covergroup config_cg;
		option.per_instance = 1;
		lane0_delay : coverpoint lane_delays[0]
		{bins delay[] = {[0:7]};}
		lane1_delay : coverpoint lane_delays[1]
		{bins delay[] = {[0:7]};}
		lane2_delay : coverpoint lane_delays[2]
		{bins delay[] = {[0:7]};}
		lane3_delay : coverpoint lane_delays[3]
		{bins delay[] = {[0:7]};}
		lane4_delay : coverpoint lane_delays[4]
		{bins delay[] = {[0:7]};}
		lane5_delay : coverpoint lane_delays[5]
		{bins delay[] = {[0:7]};}
		lane6_delay : coverpoint lane_delays[6]
		{bins delay[] = {[0:7]};}
		lane7_delay : coverpoint lane_delays[7]
		{bins delay[] = {[0:7]};}
		lane8_delay : coverpoint lane_delays[8]
		{bins delay[] = {[0:7]};}
		lane9_delay : coverpoint lane_delays[9]
		{bins delay[] = {[0:7]};}
		lane10_delay : coverpoint lane_delays[10]
		{bins delay[] = {[0:7]};}
		lane11_delay : coverpoint lane_delays[11]
		{bins delay[] = {[0:7]};}
		lane12_delay : coverpoint lane_delays[12]
		{bins delay[] = {[0:7]};}
		lane13_delay : coverpoint lane_delays[13]
		{bins delay[] = {[0:7]};}
		lane14_delay : coverpoint lane_delays[14]
		{bins delay[] = {[0:7]};}
		lane15_delay : coverpoint lane_delays[15]
		{bins delay[] = {[0:7]};}

		lane0_polarity : coverpoint reverse_polarity[0]
		{bins polarity = {1};}
		lane1_polarity : coverpoint reverse_polarity[1]
		{bins polarity = {1};}
		lane2_polarity : coverpoint reverse_polarity[2]
		{bins polarity = {1};}
		lane3_polarity : coverpoint reverse_polarity[3]
		{bins polarity = {1};}
		lane4_polarity : coverpoint reverse_polarity[4]
		{bins polarity = {1};}
		lane5_polarity : coverpoint reverse_polarity[5]
		{bins polarity = {1};}
		lane6_polarity : coverpoint reverse_polarity[6]
		{bins polarity = {1};}
		lane7_polarity : coverpoint reverse_polarity[7]
		{bins polarity = {1};}
		lane8_polarity : coverpoint reverse_polarity[8]
		{bins polarity = {1};}
		lane9_polarity : coverpoint reverse_polarity[9]
		{bins polarity = {1};}
		lane10_polarity : coverpoint reverse_polarity[10]
		{bins polarity = {1};}
		lane11_polarity : coverpoint reverse_polarity[11]
		{bins polarity = {1};}
		lane12_polarity : coverpoint reverse_polarity[12]
		{bins polarity = {1};}
		lane13_polarity : coverpoint reverse_polarity[13]
		{bins polarity = {1};}
		lane14_polarity : coverpoint reverse_polarity[14]
		{bins polarity = {1};}
		lane15_polarity : coverpoint reverse_polarity[15]
		{bins polarity = {1};}

	endgroup

	`uvm_object_utils_begin(hmc_local_link_config)
		`uvm_field_int(reverse_polarity, UVM_DEFAULT | UVM_BIN)
		`uvm_field_int(reverse_lanes, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(lane_delays_enabled, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(irtry_flit_count_to_send, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(irtry_flit_count_received_threshold, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(random_retry_probability, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(max_retry_attempts, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(poisoned_packets_minimum_length, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(poisoned_probability, UVM_DEFAULT| UVM_DEC)
		`uvm_field_int(lng_error_probability, UVM_DEFAULT| UVM_DEC)
		`uvm_field_int(seq_error_probability, UVM_DEFAULT| UVM_DEC)
		`uvm_field_int(crc_error_probability, UVM_DEFAULT| UVM_DEC)
		`uvm_field_int(bitflip_error_probability, UVM_DEFAULT| UVM_DEC)
		`uvm_field_int(width, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(send_pret_time, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(send_tret_time, UVM_DEFAULT | UVM_DEC)
		`uvm_field_enum(uvm_active_passive_enum, active, UVM_DEFAULT)
		`uvm_field_int(run_length_limit, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(requester, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(errors_enabled, UVM_DEFAULT)
		`uvm_field_int(lane_errors_enabled, UVM_DEFAULT)
		
	`uvm_object_utils_end

//	constraint c_token_count {
//		token_count > 27 && token_count < 1024;	//token count min=27, for compliance with tx_link. Could be refined if necessary
//	}

	constraint c_max_retry_attempts {
		max_retry_attempts == 10;
	}
	
	constraint c_TS1_Messages {
		soft TS1_Messages == 6;
	}
	
	constraint c_active_settings {
		active==UVM_ACTIVE ||
			random_retry_probability == 0 && send_pret_time == 0 &&
			send_tret_time == 0;// && bit_errors_allowed == 0;// &&
		//	poisoned_packets_allowed == 0;
	}

	constraint c_lane_delays {
		foreach (lane_delays[i]) {
			if(lane_delays_enabled) lane_delays[i] inside {[0:7]};
			else lane_delays[i]==0;
		}
	}
	
	constraint c_lane_polarity {
		foreach (reverse_polarity[i]) {
			if ((width == 8) && (i >=8)) reverse_polarity[i] == 0; 
		}
	}

	constraint c_send_pret_time {
		send_pret_time == 0;
	}

	constraint c_send_tret_time {
		send_tret_time == 0;
	}

	constraint c_irtry_flit_count_received_threshold {
		irtry_flit_count_received_threshold  == 16;
	}
	constraint c_irtry_flit_count_to_send {
		//irtry_flit_count_to_send > 16 && irtry_flit_count_to_send < 30;
		irtry_flit_count_to_send == 16;
	}

	constraint c_poisoned_packets_propability {
		poisoned_probability <=10;
		poisoned_probability >=0;
		
		soft poisoned_probability == 0;
		if (errors_enabled) (poisoned_probability == 6);
	}
	
	constraint c_lng_error_probability {
		lng_error_probability <=10;
		lng_error_probability >=0;
		
		soft lng_error_probability == 0;
		if (errors_enabled) (lng_error_probability == 6);
	}
	
	constraint c_seq_error_probability {
		seq_error_probability <=10;
		seq_error_probability >=0;
		
		soft seq_error_probability == 0;
		if (errors_enabled) (seq_error_probability == 6);
	}
	
	constraint c_crc_error_probability {
		crc_error_probability <=10;
		crc_error_probability >=0;
		
		soft crc_error_probability == 0;
		if (errors_enabled)(crc_error_probability == 6);
	}
	
	constraint c_bitflip_error_probability {
		soft bitflip_error_probability == 0;
		if (lane_errors_enabled)(bitflip_error_probability == 2);
	}

	constraint c_poisoned_packets_minimum_length {
		poisoned_packets_minimum_length > 4 &&
		poisoned_packets_minimum_length < 9;
	}

	function new(string name="hmc_local_link_config");
		super.new(name);
		config_cg = new();
	endfunction : new

	function void post_randomize();
	endfunction : post_randomize

	virtual function void do_print (uvm_printer printer);
		super.do_print(printer);
	endfunction : do_print

endclass : hmc_local_link_config

class hmc_link_config extends uvm_object;

	// Global Configuration (Requester, Responder, and Monitor)
	rand bit [2:0]  	cube_id; 
	rand bit 			scramblers_enabled;
	// Timing parameters
	int tINIT = 1us;  // 20ms in the spec, but that would take too long in simulation
	int tRESP1 = 1us; // 1us or 1.2ms with DFE
	int tRESP2 = 1us; // 1us

	int fpw;	//-- used for coverage

	time t_PST = 80ns;
	time t_SS =  500ns;
	time t_SME = 600ns;

	int retry_timeout_period = 614.4ns; // 10Gbps
							// 491.52ns // 12.5Gbps
							// 409.35ns // 15Gbps

	rand int	bit_rate;
	rand int	bit_time;
	
	rand int 	hmc_tokens;
	rand int 	rx_tokens;
	
	
	uvm_active_passive_enum	cfg_rsp_open_loop = UVM_PASSIVE; 
	uvm_active_passive_enum enable_tag_checking = UVM_ACTIVE;

	// Configure the Requester
	hmc_local_link_config requester;
	hmc_local_link_config responder;

	`uvm_object_utils_begin(hmc_link_config)
		`uvm_field_int(tINIT, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(tRESP1, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(tRESP2, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(retry_timeout_period, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(scramblers_enabled, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(bit_rate, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(bit_time, UVM_DEFAULT | UVM_DEC)
		`uvm_field_object(requester, UVM_DEFAULT)
		`uvm_field_object(responder, UVM_DEFAULT)
		`uvm_field_int(hmc_tokens, UVM_DEC)
		`uvm_field_int(rx_tokens, UVM_DEC)
		`uvm_field_enum(uvm_active_passive_enum, cfg_rsp_open_loop, UVM_DEFAULT)
		`uvm_field_enum(uvm_active_passive_enum, enable_tag_checking, UVM_DEFAULT)

	`uvm_object_utils_end
	
	//-- Constraints
	
	constraint cube_id_c {
		cube_id >= 0;
		soft cube_id == 0; 
	}

	constraint c_bit_rate {
							// Eventually allow 10, 12.5, and 15 Gb/s
		bit_rate == 10_000; //10Gbit/s = 10_000 Mbit/s
	}

	constraint c_bit_time {
		//bit_time > 0 && bit_time == 1us/bit_rate;
		bit_time == 100ps; // 10Gbit
		//bit_time == 80ps; // 12.5Gbit
		//bit_time == 66ps; // 15Gbit TODO: Rounding problems?!?
	}
	
	constraint hmc_tokens_c {
		hmc_tokens >= 25;
		soft hmc_tokens dist{[25:30]:/5, [31:219]:/95};
	}
	
	constraint rx_tokens_c {
		rx_tokens >=30;
		soft rx_tokens dist{[9:30]:/5, [31:255]:/95};
	}

	function new(string name="hmc_link_config");
		super.new(name);
		requester = new;
		responder = new;
	endfunction : new

	function void post_randomize();
		assert (requester.randomize());
		assert (responder.randomize());
	endfunction : post_randomize

	virtual function void do_print (uvm_printer printer);
		super.do_print(printer);
		requester.do_print(printer);
		responder.do_print(printer);
	endfunction : do_print

endclass : hmc_link_config

`endif // hmc_config_SV
