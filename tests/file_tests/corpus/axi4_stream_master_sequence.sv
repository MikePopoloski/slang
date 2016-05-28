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

`ifndef AXI4_STREAM_MASTER_SEQUENCE_SV
`define AXI4_STREAM_MASTER_SEQUENCE_SV

class axi4_stream_master_sequence extends uvm_sequence;

	rand int delay;
	rand hmc_packet response;
	rand bit error_response;
    event item_available;

	hmc_packet response_queue[$];
	
	constraint delay_c {
		delay dist {0:=4, [0:9]:=8, [10:30]:=2, [31:100]:=1};
	}

	`uvm_object_utils(axi4_stream_master_sequence)
	
	`uvm_declare_p_sequencer(axi4_stream_master_sequencer)

	function new(string name="axi4_stream_master_sequence");
		super.new(name);
	endfunction : new

	task body();
		
		void'(this.randomize());
		
		fork
			// Convert requests to responses
			forever begin : tranlsate_loop
				hmc_packet packet;
				p_sequencer.req_mailbox.get(packet);
				create_response_packet(packet);
			end : tranlsate_loop
			
			// 
			begin
				hmc_packet packet;
				
				forever begin : send_loop
					
					if (response_queue.size() > 0) begin
						int time_to_wait;

						time_to_wait = response_queue[0].timestamp - $time;
						if (time_to_wait <= 0) begin
							packet = response_queue.pop_front();
							uvm_report_info(get_type_name(), $psprintf("Sending response packet: %s", packet.command.name()), UVM_HIGH);
							`uvm_send(packet)
						end else begin
							#time_to_wait;
						end
					end
					else begin
						// Wait for items to get added to the queue
						if (response_queue.size() == 0)
							@(item_available);
					end
					
				end : send_loop
			end
		join
		
	endtask : body

endclass : axi4_stream_master_sequence

`endif // AXI4_STREAM_MASTER_SEQUENCER_SV

