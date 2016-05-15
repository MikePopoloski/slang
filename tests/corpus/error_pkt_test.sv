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
// error_pkt_test test
//
//

`ifndef error_pkt_test_SV
`define error_pkt_test_SV

class error_pkt_test extends hmc_base_test;

	`uvm_component_utils(error_pkt_test)


	function new(string name = "error_pkt_test", uvm_component parent = null);
		super.new(name,parent);
	endfunction : new


	virtual function void build_phase(uvm_phase phase);
		
		uvm_config_db#(uvm_object_wrapper)::set(this,"hmc_tb0.v_seqr.run_phase","default_sequence",error_pkt_test_seq::type_id::get());
		super.build_phase(phase);
		link_cfg.requester.errors_enabled = 1;
		link_cfg.responder.errors_enabled = 1;
		
		link_cfg.requester.lane_errors_enabled = 0;
		link_cfg.responder.lane_errors_enabled = 0;
		
		link_cfg_randomize : assert (link_cfg.randomize());
	endfunction : build_phase
	
	task run_phase(uvm_phase phase);
		phase.phase_done.set_drain_time(this, 1us);
	endtask : run_phase

endclass : error_pkt_test

`endif // error_pkt_test_SV