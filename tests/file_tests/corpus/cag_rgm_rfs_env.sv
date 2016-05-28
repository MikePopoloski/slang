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

`ifndef CAG_RGM_RFS_ENV_SV
`define CAG_RGM_RFS_ENV_SV

class cag_rgm_rfs_env #(
		parameter ADDR_WIDTH	   = 6,
		parameter WRITE_DATA_WIDTH = 64,
		parameter READ_DATA_WIDTH  = 64
	) extends uvm_env;

	uvm_active_passive_enum is_active = UVM_ACTIVE;

	cag_rgm_rfs_driver  #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)) driver;
	cag_rgm_rfs_monitor #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)) monitor;

	cag_rgm_sequencer   sequencer;
	
	`uvm_component_param_utils_begin(cag_rgm_rfs_env  #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)))
		`uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
	`uvm_component_utils_end
	
	function new(string name="cag_rgm_rfs_env", uvm_component parent);
		super.new(name,parent);
	endfunction : new
	
	function void build();
		super.build();
		
		monitor = cag_rgm_rfs_monitor #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH))::type_id::create("monitor",this);
		
		if(is_active == UVM_ACTIVE) begin
			driver = cag_rgm_rfs_driver  #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH))::type_id::create("driver",this);
			
			sequencer = cag_rgm_sequencer::type_id::create("sequencer",this);
		end
		
	endfunction : build
	
	function void connect();
		super.connect();
		
		if(is_active == UVM_ACTIVE) begin
			driver.seq_item_port.connect(sequencer.seq_item_export);
			monitor.response_port.connect(sequencer.resp_port);
		end
	endfunction : connect
	
	function void assign_vi( virtual interface cag_rgm_rfs_if #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)) vif);
		monitor.assign_vi(vif);
		if(is_active == UVM_ACTIVE)
			driver.assign_vi(vif);
	endfunction : assign_vi
	
	function void set_rf(cag_rgm_register_file rf);
		if(is_active == UVM_ACTIVE)
			sequencer.set_rf(rf);
	endfunction : set_rf

endclass : cag_rgm_rfs_env

`endif // CAG_RGM_RFS_ENV_SV
