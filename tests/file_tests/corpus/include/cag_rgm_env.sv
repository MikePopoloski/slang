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

`ifndef CAG_RGM_ENV_SV
`define CAG_RGM_ENV_SV

class cag_rgm_env extends uvm_env;
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;

    `uvm_component_utils_begin(cag_rgm_env)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
    `uvm_component_utils_end
	
	cag_rgm_sequencer sequencer;
	
	cag_rgm_monitor tx_monitor;
	cag_rgm_monitor rx_monitor;
	
	function new(string name="cag_rgm_env", uvm_component parent);
		super.new(name,parent);
	endfunction : new
	
	function void build();
		super.build();
		
		if(is_active == UVM_ACTIVE)
			sequencer = cag_rgm_sequencer::type_id::create("sequencer",this);
		
		tx_monitor = cag_rgm_monitor::type_id::create("tx_monitor",this);
		rx_monitor = cag_rgm_monitor::type_id::create("rx_monitor",this);
		
	endfunction : build
	
	function void connect();
		if(is_active == UVM_ACTIVE) begin
			rx_monitor.collected_port.connect(sequencer.resp_port);
		end
	endfunction : connect
	
	function void set_rf(cag_rgm_register_file rf);
		if(is_active == UVM_ACTIVE)
			sequencer.set_rf(rf);
	endfunction : set_rf
	
endclass : cag_rgm_env

`endif // CAG_RGM_ENV_SV
