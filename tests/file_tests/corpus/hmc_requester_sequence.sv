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
`ifndef HMC_REQUESTER_SEQUENCE_SV
`define HMC_REQUESTER_SEQUENCE_SV

/* sequence is incomplete and not tested */
/* Use at your own risk */

class hmc_requester_sequence extends uvm_sequence;

	rand int delay;
	rand hmc_packet response;
	rand bit error_response;
    event item_available;

	hmc_packet response_queue[$];

	constraint delay_c {
		delay dist {0:=4, [0:9]:=8, [10:30]:=2, [31:100]:=1};
	}

	`uvm_object_utils(hmc_requester_sequence)

	`uvm_declare_p_sequencer(hmc_requester_sequencer)

	function new(string name="hmc_requester_sequence");
		super.new(name);
	endfunction : new

	task create_response_packet(hmc_packet request);
		int response_length = 1;
		int new_timestamp;
		bit [127:0] rand_flit;
		bit [127:0] payload_flits [$];

		`uvm_info(get_type_name(),$psprintf("Generating response for a %s @%0x",request.command.name(), request.address),UVM_HIGH)

		`uvm_create(response);

		void'(this.randomize(error_response));
		void'(this.randomize(delay));

		new_timestamp = delay * 500ps + $time;

		if (request.get_command_type() == HMC_READ_TYPE) begin : read

			case (request.command)
				HMC_READ_16 : response_length = 2;
				HMC_READ_32 : response_length = 3;
				HMC_READ_48 : response_length = 4;
				HMC_READ_64 : response_length = 5;
				HMC_READ_80 : response_length = 6;
				HMC_READ_96 : response_length = 7;
				HMC_READ_112 : response_length = 8;
				HMC_READ_128 : response_length = 9;
			endcase

			// Randomize the packet
			void'(response.randomize() with {
				command == HMC_READ_RESPONSE;
				address == request.address; // for debugging
				packet_length == response_length;
				duplicate_length == response_length;
				tag == request.tag;
				error_status == 0 || error_response;
			});

			for (int i=0; i<response_length-1; i++) begin
				randomize_flit_successful : assert (std::randomize(rand_flit))
				payload_flits.push_front(rand_flit);
			end

			response.payload = payload_flits;
			response.timestamp = new_timestamp;
			enqueue_response_packet(response);

		end : read
		else if (request.get_command_type() == HMC_WRITE_TYPE) begin : write

			response_length = 1;

			void'(response.randomize() with {
				command == HMC_WRITE_RESPONSE;
				address == request.address; // for debugging
				packet_length == response_length;
				duplicate_length == response_length;
				tag == request.tag;
				error_status == 0 || error_response;
			});

			response.timestamp = new_timestamp;
			enqueue_response_packet(response);

		end : write
		// Posted Writes are allowed, but get no response
		else if (	request.get_command_type() != HMC_POSTED_WRITE_TYPE ||
					request.get_command_type() != HMC_POSTED_MISC_WRITE_TYPE
		) begin : error
			uvm_report_fatal(get_type_name(), $psprintf("Unsupported command type %s", request.command.name()));
		end : error

	endtask : create_response_packet

	task enqueue_response_packet(hmc_packet response);
			// Insert at the end when the queue is empty or
		if (response_queue.size() == 0 ||
			// when the timestamp is larger than the tail of the queue
			response.timestamp >= response_queue[response_queue.size()-1].timestamp) begin
			response_queue.push_back(response);
			// Insert at the beginning of the queue when the timestamp is small
		end else if (response.timestamp <= response_queue[0].timestamp) begin
			response_queue.push_front(response);
		end else begin
			for (int position=1;position < response_queue.size(); position++) begin
				if (response.timestamp < response_queue[position].timestamp) begin
					response_queue = {response_queue[0:position-1], response, response_queue[position:$]};
					position = response_queue.size(); // Break
				end
			end
		end

			// Signal via event that a response has been added
			-> item_available;

	endtask : enqueue_response_packet

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

endclass : hmc_requester_sequence

`endif // HMC_REQUESTER_SEQUENCE_SV

