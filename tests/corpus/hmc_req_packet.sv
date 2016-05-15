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
// hmc_req_packet
//

// Only requests should be sent to test the controller
// All of the tail fields should be zero

`ifndef HMC_REQ_PACKET_SV
`define HMC_REQ_PACKET_SV

class hmc_req_packet extends hmc_packet;
`uvm_object_utils(hmc_req_packet)

	constraint req_command_c {
		   command inside { 	HMC_WRITE_16,
			   					HMC_WRITE_32,
			   					HMC_WRITE_48,
			   					HMC_WRITE_64,
			   					HMC_WRITE_80,
			   					HMC_WRITE_96,
			   					HMC_WRITE_112,
			   					HMC_WRITE_128,
			   					
			   					//HMC_MODE_WRITE,
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
			   					
			   			//		HMC_MODE_READ,
			   					HMC_READ_16,
			   					HMC_READ_32,
			   					HMC_READ_48,
			   					HMC_READ_64,
			   					HMC_READ_80,
			   					HMC_READ_96,
			   					HMC_READ_112, 
			   					HMC_READ_128
			   
			   				};
	}


	constraint c_zero_tail_fields {
		return_token_count == 0; 
		sequence_number == 0; 
		forward_retry_pointer == 0; 
		return_retry_pointer == 0; 
		packet_crc == 0; 
	}

	function new (string name = "hmc_req_packet");
		super.new(name);
	endfunction : new

endclass : hmc_req_packet

`endif // HMC_REQ_PACKET_SV

