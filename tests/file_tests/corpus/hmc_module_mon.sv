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

`ifndef MODULE_MON
`define MODULE_MON
class hmc_module_mon extends uvm_monitor;
	//-- Basic Module monitor
	hmc_packet packet;
	

	covergroup hmc_pkt_cg;
		option.per_instance = 1;
		HMC_PACKET_LENGTH : coverpoint packet.packet_length{
			illegal_bins zero_flit_pkt = {0};
			bins pkt_length[] = {[1:9]};
		}
		HMC_COMMAND: coverpoint packet.command {
			bins requests[] = {
				HMC_WRITE_16,
				HMC_WRITE_32,
				HMC_WRITE_48,
				HMC_WRITE_64,
				HMC_WRITE_80,
				HMC_WRITE_96,
				HMC_WRITE_112,
				HMC_WRITE_128,
				
				HMC_MODE_WRITE,
				HMC_BIT_WRITE,
				HMC_DUAL_8B_ADDI,
				HMC_SINGLE_16B_ADDI,
				
				HMC_POSTED_WRITE_16,
				HMC_POSTED_WRITE_32,
				HMC_POSTED_WRITE_48,
				HMC_POSTED_WRITE_64,
				HMC_POSTED_WRITE_80,
				HMC_POSTED_WRITE_96,
				HMC_POSTED_WRITE_112,
				HMC_POSTED_WRITE_128,
				HMC_POSTED_BIT_WRIT,
				
				HMC_POSTED_BIT_WRIT,
				HMC_POSTED_DUAL_8B_ADDI,
				HMC_POSTED_SINGLE_16B_ADDI,
				
				HMC_MODE_READ,
				HMC_READ_16,
				HMC_READ_32,
				HMC_READ_48,
				HMC_READ_64,
				HMC_READ_80,
				HMC_READ_96,
				HMC_READ_112, 
				HMC_READ_128};

			bins response[] = {
				HMC_READ_RESPONSE,
				HMC_WRITE_RESPONSE,
				HMC_MODE_READ_RESPONSE,
				HMC_MODE_WRITE_RESPONSE,
				HMC_ERROR_RESPONSE
			};
	
			illegal_bins n_used = default;
		}
		FLIT_DELAY: coverpoint packet.flit_delay{
			bins zero_delay = {0};
			bins small_delay = {[1:3]};
			bins big_delay = {[4:20]};
			bins huge_delay = {[21:$]};
		}
		FLIT_DELAY_COMMAND : cross HMC_COMMAND, FLIT_DELAY;
		
	endgroup
	
	uvm_analysis_port #(hmc_packet) item_collected_port;
	int req_rcvd = 0;
	int rsp_rcvd = 0;
	
	
	`uvm_component_utils(hmc_module_mon)
	function new ( string name = "hmc_module_mon", uvm_component parent );
		super.new(name, parent);
		item_collected_port = new("item_collected_port", this);
	endfunction : new


	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction : build_phase
	
	
endclass

`endif