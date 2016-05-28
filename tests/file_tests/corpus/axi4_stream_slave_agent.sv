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

`ifndef AXI4_STREAM_SLAVE_AGENT_SV
`define AXI4_STREAM_SLAVE_AGENT_SV

class axi4_stream_slave_agent #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends uvm_agent;

	axi4_stream_config axi4_stream_cfg;
	virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) vif;

	axi4_stream_slave_driver #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) driver;

	`uvm_component_param_utils_begin(axi4_stream_slave_agent #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))
		`uvm_field_object(axi4_stream_cfg, UVM_DEFAULT)
	`uvm_component_utils_end

	function new(string name="axi4_stream_slave_agent", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if(uvm_config_db#(virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))::get(this, "", "vif",vif) ) begin
			uvm_config_db#(virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))::set(this, "driver","vif",vif);		
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")	
		end
		if (!uvm_config_db#(axi4_stream_config)::get(this, "", "axi4_stream_cfg", axi4_stream_cfg)) begin
			uvm_report_fatal(get_type_name(), $psprintf("axi4_stream_cfg not set via config_db"));
		end else begin
			uvm_config_db#(axi4_stream_config)::set(this, "driver"	, "axi4_stream_cfg", axi4_stream_cfg);			//distributing axi4_stream_cfg to master driver
		end
		
		if(axi4_stream_cfg.slave_active == UVM_ACTIVE)begin
			uvm_config_db#(axi4_stream_config)::set(this, "driver", "axi4_stream_cfg", axi4_stream_cfg);		// distribute axi4_stream_cfg to driver
			driver        = axi4_stream_slave_driver#(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH))::type_id::create("driver", this);
		end

	endfunction : build_phase

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction : connect_phase

endclass : axi4_stream_slave_agent

`endif // AXI4_STREAM_SLAVE_AGENT_SV
