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

`ifndef hmc_VIRTUAL_SEQUENCER_SV
`define hmc_VIRTUAL_SEQUENCER_SV

class  vseqr extends uvm_sequencer;

	hmc_link_config link_cfg;
	
	cls_link_cfg hmc_link_cfg;

	//-- references to testbench sequencers
    cag_rgm_sequencer rf_seqr_hmc;
	
	hmc_module_scb scb;
		
	hmc_2_axi4_sequencer #(.DATA_BYTES(`AXI4BYTES),.TUSER_WIDTH(`AXI4BYTES))  axi4_req_seqr;

	`uvm_component_utils_begin(vseqr)
		`uvm_field_object(link_cfg, UVM_DEFAULT)
	`uvm_component_utils_end
	
	function new (string name = "hmc_virtual_sequencer", uvm_component parent);
		super.new(name, parent);
		
		hmc_link_cfg = new();
	endfunction : new
	
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		if (!uvm_config_db#(hmc_link_config)::get(this, "", "link_cfg", link_cfg)) begin
			uvm_report_fatal(get_type_name(), $psprintf("hmc_link_config not set via config_db"));
		end
		
			
	endfunction : build_phase
	
	
	//function void connect_phase(uvm_phase phase);
	//	
	//endfunction : connect_phase
	

endclass : vseqr

`endif // hmc_VIRTUAL_SEQUENCER_SV
