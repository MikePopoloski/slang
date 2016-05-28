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
// axi4_valid_cycle
//

`ifndef AXI4_STREAM_VALID_CYCLE_SV
`define AXI4_STREAM_VALID_CYCLE_SV

class axi4_stream_valid_cycle #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends uvm_sequence_item;

	rand bit [DATA_BYTES*8-1:0]	tdata;
	rand bit [TUSER_WIDTH-1:0]	tuser;
	rand int unsigned 			delay = 0;
	
	constraint c_packet_delay {
		delay < 20 ;
	}
	

	`uvm_object_param_utils_begin(axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))
		`uvm_field_int(tdata, UVM_ALL_ON | UVM_NOPACK | UVM_HEX)
		`uvm_field_int(tuser, UVM_ALL_ON | UVM_NOPACK | UVM_HEX)
		`uvm_field_int(delay, UVM_DEFAULT | UVM_DEC| UVM_NOPACK)
	`uvm_object_utils_end

	function new (string name = "axi4_stream_valid_cycle");
		super.new(name);
	endfunction : new

endclass : axi4_stream_valid_cycle

`endif // AXI4_STREAM_VALID_CYCLE_SV

