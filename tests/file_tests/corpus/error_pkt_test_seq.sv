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
// error_pkt_test sequence
//
//

`ifndef error_pkt_test_SEQ_SV
`define error_pkt_test_SEQ_SV

class error_pkt_test_seq extends hmc_base_seq;

	rand int iterations;
	
	constraint iterations_c {
		iterations >= 1;
		iterations <= 20;
	}

	function new(string name="error_pkt_test_seq");
		super.new(name);
	endfunction : new

	openhmc_init_seq init;
	hmc_model_init_seq bfm;
	openhmc_check_seq check;
	hmc_base_pkt_seq work;

	`uvm_object_utils(error_pkt_test_seq)
	`uvm_declare_p_sequencer(vseqr)
	
	hmc_2_axi4_sequence #(.DATA_BYTES(`AXI4BYTES), .TUSER_WIDTH(`AXI4BYTES)) requests;

	virtual task body();

		`uvm_info(get_type_name(), "starting error_pkt_test_seq", UVM_NONE)
		
    	`uvm_do(bfm)
		#1us;
        `uvm_do(init)
        #1us;	

		repeat (iterations) 
			randcase
				1 : `uvm_do_with(work, {req_class == NON_POSTED;})
				1 : `uvm_do_with(work, {req_class == POSTED;})
		endcase

		`uvm_info(get_type_name(), "error_pkt_test_seq done", UVM_NONE)
		`uvm_do(check)

	endtask : body

endclass : error_pkt_test_seq

`endif // error_pkt_test_SEQ_SV
