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

//
//
// hmc_2_axi4_sequencer
//
//

`ifndef HMC_2_AXI4_SEQUENCER_SV
`define HMC_2_AXI4_SEQUENCER_SV

typedef class hmc_2_axi4_sequence;

class hmc_2_axi4_sequencer #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends axi4_stream_master_sequencer #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH));

 	tag_handler  handler;	//-- a tag handler is used to handle tags of non posted packets
	
	`uvm_component_param_utils_begin(hmc_2_axi4_sequencer #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))
		`uvm_field_object(handler, UVM_DEFAULT)
	`uvm_component_utils_end
	function new (string name = "hmc_2_axi4_sequencer", uvm_component parent);
		super.new(name, parent);
		
	endfunction : new

	
	function void build_phase(uvm_phase phase);
		handler = tag_handler::type_id::create("handler", this);
	endfunction : build_phase
endclass : hmc_2_axi4_sequencer

`endif // HMC_2_AXI4_SEQUENCER_SV

