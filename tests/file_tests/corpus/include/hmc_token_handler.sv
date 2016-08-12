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
`ifndef HMC_TOKEN_HANDLER_SV
`define HMC_TOKEN_HANDLER_SV

class hmc_token_handler extends uvm_component;
	
	`uvm_analysis_imp_decl(_tokens)
	uvm_analysis_imp_tokens#(hmc_packet, hmc_token_handler) token_imp;


	`uvm_component_utils(hmc_token_handler)

	int available_tokens;
	
	function new(string name="hmc_token_handler", uvm_component parent);
		super.new(name,parent);
		
		token_imp = new ("token_imp",this);
		available_tokens = 0;
	endfunction : new

	function void reset();
		available_tokens = 0;
	endfunction : reset

	function void write_tokens(input hmc_packet packet);
		//`uvm_info(get_type_name(), $psprintf("write_tokens received %0d available_tokens = %0d", packet.return_token_count, available_tokens), UVM_HIGH)
		available_tokens = available_tokens + packet.return_token_count;
	endfunction : write_tokens

	function bit tokens_available(input int request);
		//`uvm_info(get_type_name(), $psprintf("tokens_available called for %0d available_tokens = %0d", request, available_tokens), UVM_HIGH)
		tokens_available = 0;
		if (available_tokens >= request) begin
			available_tokens = available_tokens - request;
			tokens_available = 1;
		end
	endfunction : tokens_available
	
		
endclass : hmc_token_handler

`endif // HMC_TOKEN_HANDLER_SV
