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
`ifndef HMC_RESPONDER_SEQUENCER_SV
`define HMC_RESPONDER_SEQUENCER_SV

typedef class hmc_responder_sequence;

class hmc_responder_sequencer extends uvm_sequencer #(hmc_packet);

    `uvm_analysis_imp_decl(_hmc_req)
    uvm_analysis_imp_hmc_req #(hmc_packet, hmc_responder_sequencer) hmc_req_port;
    mailbox #(hmc_packet) req_mailbox;

	`uvm_component_utils(hmc_responder_sequencer)

	hmc_responder_sequence resp_seq;
	
	function new(string name="hmc_responder_sequencer", uvm_component parent);
		super.new(name,parent);
        hmc_req_port     = new("hmc_req_port", this); 
        req_mailbox    = new();
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	
	endfunction : build_phase
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		
	endfunction : connect_phase
	
	task run();
		resp_seq = hmc_responder_sequence::type_id::create("resp_seq", this);
		resp_seq.start(this);
	endtask : run

	virtual function void write_hmc_req(input hmc_packet request);

		`uvm_info(get_type_name(),$psprintf("Request: %s",request.command.name()),UVM_HIGH)

		req_mailbox_not_full : assert (req_mailbox.try_put(request));

	endfunction : write_hmc_req

endclass : hmc_responder_sequencer

`endif // HMC_RESPONDER_SEQUENCER_SV

