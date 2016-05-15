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

`ifndef hmc_BASE_TEST_SV
`define hmc_BASE_TEST_SV

class hmc_base_test extends uvm_test;

	hmc_tb hmc_tb0;
	axi4_stream_config axi4_req_config;
	axi4_stream_config axi4_rsp_config;
	
	hmc_link_config link_cfg;

	uvm_table_printer printer;

	function new(string name="hmc_base_test", uvm_component parent=null);
		super.new(name,parent);
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		//-- create config
		
		//-- AXI4 request config
		axi4_req_config = axi4_stream_config::type_id::create("axi4_req_config", this);
		axi4_req_config.master_active = UVM_ACTIVE;
		axi4_req_config.slave_active  = UVM_PASSIVE;
		axi4_req_config.open_rsp_mode  = UVM_PASSIVE;

		uvm_report_info(get_type_name(), $psprintf("Setting the axi4_req config:\n"), UVM_LOW);
		uvm_config_db#(axi4_stream_config)::set(this, "hmc_tb0", "axi4_req_config", axi4_req_config);
		
		//-- AXI4 response config
		axi4_rsp_config = axi4_stream_config::type_id::create("axi4_rsp_config", this);
		axi4_rsp_config.master_active = UVM_PASSIVE;
		axi4_rsp_config.slave_active = UVM_ACTIVE;
		axi4_rsp_config.open_rsp_mode = `OPEN_RSP_MODE==1 ? UVM_ACTIVE : UVM_PASSIVE;

		uvm_report_info(get_type_name(), $psprintf("Setting the axi4_rsp config:\n"), UVM_LOW);
		uvm_config_db#(axi4_stream_config)::set(this, "hmc_tb0", "axi4_rsp_config", axi4_rsp_config);
		
		//-- HMC link config
		link_cfg = hmc_link_config::type_id::create("link_cfg",this);
		link_cfg.cfg_rsp_open_loop = `OPEN_RSP_MODE==1 ? UVM_ACTIVE : UVM_PASSIVE;
		void'(link_cfg.randomize());
		
		uvm_config_db#(hmc_link_config)::set(this, "hmc_tb0", "link_cfg", link_cfg);
		

		set_config_int("*", "recording_detail", UVM_FULL);
		
		//-- create the testbench
		hmc_tb0 = hmc_tb#()::type_id::create("hmc_tb0", this);

		printer = new();
		printer.knobs.depth = 5;

	endfunction : build_phase

	function void end_of_elaboration_phase(uvm_phase phase);
		super.end_of_elaboration_phase(phase);

		uvm_report_info(get_type_name(), $psprintf("Printing the test topology :\n%s", this.sprint(printer)), UVM_HIGH);

	endfunction : end_of_elaboration_phase


	virtual task run_phase(uvm_phase phase);
		phase.phase_done.set_drain_time(this, 10us);
	endtask : run_phase

endclass : hmc_base_test


class hmc_base_seq extends uvm_sequence;

	function new(string name="hmc_base_seq");
		super.new(name);
	endfunction : new

	`uvm_object_utils(hmc_base_seq)
	`uvm_declare_p_sequencer(vseqr)

	virtual task pre_body();
		if(starting_phase != null)
			starting_phase.raise_objection(this);
	endtask : pre_body

	virtual task post_body();
		if(starting_phase != null)
			starting_phase.drop_objection(this);
	endtask : post_body

endclass : hmc_base_seq

`endif // hmc_BASE_TEST_SV
