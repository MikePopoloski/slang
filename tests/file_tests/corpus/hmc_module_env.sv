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

`ifndef HMC_MODULE_ENV
`define HMC_MODULE_ENV
class hmc_module_env  extends uvm_env; 
	//hmc_module_cfg module_cfg;
	
	hmc_module_mon	axi4_req_mon;
	hmc_module_mon	axi4_rsp_mon;
	
	hmc_module_mon	hmc_req_mon;
	hmc_module_mon	hmc_rsp_mon;

	
	hmc_module_scb scb;
	
	

	`uvm_component_utils(hmc_module_env)
	

	
	function new (string name = "hmc_module_env", uvm_component parent);
		super.new(name, parent);
	endfunction : new
	
	virtual function void build_phase(uvm_phase phase);
		string inst_name;
		super.build_phase(phase);
		

		
		//-- Additional monitor for AXI4 Stream 2 HMC packet conversion
		axi4_req_mon = hmc_module_mon::type_id::create("axi4_req_mon", this);
		axi4_rsp_mon = hmc_module_mon::type_id::create("axi4_rsp_mon", this);
		
		//-- Additional monitor for BFM 2 HMC packet conversion
		hmc_req_mon = hmc_module_mon::type_id::create("hmc_req_mon", this);
 		hmc_rsp_mon = hmc_module_mon::type_id::create("hmc_rsp_mon", this);
		
		//-- scoreboard
		scb = hmc_module_scb::type_id::create("scb", this);
		

	endfunction : build_phase

	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);

		//-- Connect module monitors to scoreboard 
		axi4_req_mon.item_collected_port.connect(scb.axi4_hmc_req);
		axi4_rsp_mon.item_collected_port.connect(scb.axi4_hmc_rsp);
		
		hmc_req_mon.item_collected_port.connect(scb.hmc_req_port);
		hmc_rsp_mon.item_collected_port.connect(scb.hmc_rsp_port);
		


	endfunction : connect_phase

endclass: hmc_module_env
`endif