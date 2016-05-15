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
`ifndef HMC_BASE_PKT_SEQ
`define HMC_BASE_PKT_SEQ

typedef enum {
		POSTED,
		ATOMIC,
		NON_POSTED,
		ALL_TYPES
	//	MISC
} request_class_e;

class hmc_base_pkt_seq extends hmc_base_seq;
	
	

	rand int num_packets ;
	rand int pkts_per_req;
	
	
	rand request_class_e req_class;

	//-- delay constraints
	rand int min_flit_delay  ;
	rand int max_flit_delay  ;

	rand int min_packet_length ;
	rand int max_packet_length ;
	
	

	constraint delay_c {
		!(min_flit_delay 	> max_flit_delay);
		min_flit_delay 		>= 0;		
		soft max_flit_delay	<= 50;
	}
	
	constraint pkt_length_c {
		min_packet_length <= max_packet_length;
		min_packet_length >= 0;		
		max_packet_length <= 9;
	}
	
	constraint num_packets_c {
		num_packets > 0;
		soft num_packets <= 50;
	}
	
	constraint pkts_per_req_c {
		pkts_per_req > 0;
		soft pkts_per_req <= 10;
		pkts_per_req <= num_packets;
	}
	
	`uvm_object_utils(hmc_base_pkt_seq)
	`uvm_declare_p_sequencer(vseqr)

	hmc_2_axi4_sequence #(.DATA_BYTES(`AXI4BYTES), .TUSER_WIDTH(`AXI4BYTES)) requests;

	function new(string name="hmc_base_pkt_seq");
		super.new(name);
	endfunction : new

	virtual task body();
		`uvm_info(get_type_name(), "starting...", UVM_HIGH)

		while (num_packets > 0) begin
			`uvm_create_on(requests, p_sequencer.axi4_req_seqr)
			if(req_class == POSTED)
				`uvm_info(get_type_name(),$psprintf("sending posted requests"), UVM_MEDIUM)
			else if (req_class == NON_POSTED)
				`uvm_info(get_type_name(),$psprintf("sending non_posted requests"), UVM_MEDIUM)
			else if (req_class == ATOMIC)
				`uvm_info(get_type_name(),$psprintf("sending atomic requests"), UVM_MEDIUM)
			else if (req_class == ALL)
				`uvm_info(get_type_name(),$psprintf("sending all requests"), UVM_MEDIUM)
			requests.num_packets = pkts_per_req;
			void'(requests.randomize() with {
				foreach(requests.hmc_items[i]) {
					requests.hmc_items[i].flit_delay inside {[min_flit_delay:max_flit_delay]};
					soft requests.hmc_items[i].packet_length inside {[min_packet_length:max_packet_length]};
					if(req_class == POSTED) {
						requests.hmc_items[i].command inside {
							HMC_POSTED_WRITE_16,
			   				HMC_POSTED_WRITE_32,
			   				HMC_POSTED_WRITE_48,
			   				HMC_POSTED_WRITE_64,
			   				HMC_POSTED_WRITE_80,
			   				HMC_POSTED_WRITE_96,
			   				HMC_POSTED_WRITE_112,
			   				HMC_POSTED_WRITE_128,
			   				HMC_POSTED_BIT_WRIT
						};
					}
					if(req_class == NON_POSTED) {
						requests.hmc_items[i].command inside { 
							HMC_WRITE_16,
			   				HMC_WRITE_32,
			   				HMC_WRITE_48,
			   				HMC_WRITE_64,
			   				HMC_WRITE_80,
			   				HMC_WRITE_96,
			   				HMC_WRITE_112,
			   				HMC_WRITE_128,
			   				
			   				HMC_MODE_READ,
			   				HMC_READ_16,
			   				HMC_READ_32,
			   				HMC_READ_48,
			   				HMC_READ_64,
			   				HMC_READ_80,
			   				HMC_READ_96,
			   				HMC_READ_112, 
			   				HMC_READ_128};
					}
					if(req_class == ATOMIC) {
						requests.hmc_items[i].command inside {
							//HMC_MODE_WRITE,
							HMC_BIT_WRITE,
							HMC_DUAL_8B_ADDI,
							HMC_SINGLE_16B_ADDI,
							HMC_POSTED_BIT_WRIT,
			   				
			   				HMC_POSTED_BIT_WRIT,
							HMC_POSTED_DUAL_8B_ADDI,
							HMC_POSTED_SINGLE_16B_ADDI
			   				
			//				HMC_MODE_READ
						};
					}
		//			if(req_class == MISC) {
		//				requests.hmc_items[i].command inside {
		//		//			//HMC_MODE_WRITE
		//					HMC_MODE_READ};
		//			}
					
						

				}
			});
			num_packets -= pkts_per_req;
			`uvm_info(get_type_name(),$psprintf("Packets sent!"), UVM_MEDIUM)
			
			`uvm_send(requests)
		end

	endtask : body

endclass : hmc_base_pkt_seq


`endif