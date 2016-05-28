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
 
`ifndef HMC_ERROR_INJECTOR
`define HMC_ERROR_INJECTOR

class hmc_error_injector #(parameter NUM_LANES = 16) extends uvm_component;
	
	virtual hmc_sr_if#(.NUM_LANES(NUM_LANES)) ext_vif;
	virtual hmc_sr_if#(.NUM_LANES(NUM_LANES)) int_vif;
	hmc_cdr #(.NUM_LANES(NUM_LANES)) cdr;
	
	
	hmc_link_config link_config;
	hmc_local_link_config local_config;
	hmc_link_status link_status;
	
	logic [NUM_LANES - 1 : 0] current_value;
	int num_bitflips;
	int inserted_bitflips[];

	`uvm_component_param_utils_begin(hmc_error_injector#(.NUM_LANES(NUM_LANES)))
	`uvm_component_utils_end

	function new ( string name="hmc_error_injector", uvm_component parent );
		super.new(name, parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		if(uvm_config_db#(hmc_link_config)::get(this, "", "link_config",link_config) ) begin
			uvm_config_db#(hmc_link_config)::set(this, "cdr","link_config",link_config);
		end else begin
			`uvm_fatal(get_type_name(),"link_config is not set")
		end
		
		if(!uvm_config_db#(hmc_local_link_config)::get(this, "", "local_config",local_config) ) begin
			`uvm_fatal(get_type_name(),"local_config is not set")
		end
		
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "ext_vif",ext_vif) ) begin
			this.ext_vif = ext_vif;
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end
		
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "int_vif",int_vif) ) begin
			this.int_vif = int_vif;
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end
		
		if(!uvm_config_db#(hmc_link_status)::get(this, "", "link_status",link_status) ) begin
			`uvm_fatal(get_type_name(),"link_status is not set")
		end
		
		if (local_config.requester) begin
				uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "cdr","vif",ext_vif);
		end else begin
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "cdr","vif",int_vif);
		end
		
		set_config_int("cdr", "link_type", local_config.requester?REQUESTER:RESPONDER);
		
		cdr = hmc_cdr#(.NUM_LANES(NUM_LANES))::type_id::create("cdr", this);
	endfunction : build_phase

	function void connect_phase(uvm_phase phase);
	endfunction : connect_phase


	task run_phase(uvm_phase phase);
		#1ps;
		read();
		write();
		forever begin
			@(cdr.int_clk)
			read();
			if (local_config.lane_errors_enabled && link_status.current_state >= LINK_UP)
				inject_error();
			write();
		end
	endtask : run_phase
	
	function void read();
		if (local_config.requester) begin
			current_value =  ext_vif.RXP;
		end else begin
			current_value =  int_vif.TXP;
		end
	endfunction

	function void write();
		logic [NUM_LANES - 1 : 0] inv_value;

		foreach(current_value[i]) begin
			if (!(current_value[i] === 1'bz))
				inv_value[i] = ~current_value[i];
			else begin
				inv_value[i] = 1'bz;
			end
		end

		if (local_config.requester) begin
			int_vif.RXP = current_value;
			int_vif.RXN = inv_value;
		end else begin
			ext_vif.TXP = current_value;
			ext_vif.TXN = inv_value;
		end
	endfunction : write

	function void inject_error();
		int error_probability;
		error_prob_rand_succeeds : assert (std::randomize(error_probability) 
									with {error_probability >= 0 && error_probability < 10000;});
		if (error_probability < local_config.bitflip_error_probability) begin
			num_error_rand_succeeds : assert(std::randomize(num_bitflips)
										with {num_bitflips>0 && num_bitflips<NUM_LANES;});
			`uvm_info(get_type_name(), $psprintf("Inserting %0d Bitflips in %s Link",num_bitflips, local_config.requester?"requester":"responder"), UVM_HIGH)
			bitflip(num_bitflips);
		end
	endfunction : inject_error
	
	function void bitflip(int bits);
		int pos = -1;
		int last_pos[int];
		for (int i= 0; i < bits; i++) begin
			while (last_pos[pos] == 1 || pos == -1)begin //-- inject bitflip only once per lane
				pos_randomization_succeeds : assert (std::randomize(pos) with {pos >= 0 && pos < NUM_LANES;});
			end
			last_pos[pos] = 1;
			current_value[pos] = ~current_value[pos];
			`uvm_info(get_type_name(), $psprintf("Inserting Bitflip at %d in %s Link", pos, local_config.requester?"requester":"responder"), UVM_HIGH)
		end
	endfunction : bitflip

endclass : hmc_error_injector


`endif