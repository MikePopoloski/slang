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
`ifndef HMC_RESPONDER_AGENT_SV
`define HMC_RESPONDER_AGENT_SV

class hmc_responder_agent #(parameter NUM_LANES = 16)extends uvm_agent;

	uvm_active_passive_enum active_passive = UVM_PASSIVE;

	hmc_monitor#(.NUM_LANES(NUM_LANES)) monitor;
	hmc_status h_status;
	
	hmc_responder_driver #(.NUM_LANES(NUM_LANES)) driver;
	hmc_responder_sequencer                       sequencer;
	hmc_token_handler                             token_handler;
	hmc_retry_buffer                              retry_buffer;
	
	hmc_transaction_mon req_transaction_mon;
	
	virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)) vif;

	`uvm_component_param_utils_begin(hmc_responder_agent#(.NUM_LANES(NUM_LANES)))
		`uvm_field_enum(uvm_active_passive_enum, active_passive, UVM_DEFAULT)
	`uvm_component_utils_end

	function new(string name="hmc_responder_agent", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		if(active_passive == UVM_ACTIVE) begin
			driver        = hmc_responder_driver#(.NUM_LANES(NUM_LANES))::type_id::create("driver", this);
			sequencer     = hmc_responder_sequencer::type_id::create("sequencer",this);
			token_handler = hmc_token_handler::type_id::create("token_handler",this);
			retry_buffer  = hmc_retry_buffer::type_id::create("retry_buffer",this);
		end
		
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "vif",vif) ) begin
			this.vif = vif;
			
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "driver","vif",vif);
		end
		
		if(!uvm_config_db#(hmc_status)::get(this, "", "h_status",h_status) ) begin
			`uvm_fatal(get_type_name(),"hmc_status is not set")
		end
		
	
	endfunction : build_phase

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		
		if(active_passive == UVM_ACTIVE) begin
			driver.seq_item_port.connect(sequencer.seq_item_export);

			driver.token_handler = token_handler;
			driver.retry_buffer  = retry_buffer;

			driver.remote_status = h_status.Requester_link_status;
			
			monitor.frp_port.connect(driver.hmc_frp_port);
			req_transaction_mon.transaction_finished_port.connect(sequencer.hmc_req_port);
			monitor.return_token_port.connect(token_handler.token_imp);
			monitor.rrp_port.connect(retry_buffer.return_pointer_imp);
			driver.start_clear_retry_event = monitor.start_clear_retry_event;
		end

	endfunction : connect_phase

endclass : hmc_responder_agent

`endif // HMC_RESPONDER_AGENT_SV
