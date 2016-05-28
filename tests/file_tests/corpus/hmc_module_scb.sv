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

`ifndef HMC_SCOREBOARD_SV
`define HMC_SCOREBOARD_SV


class hmc_module_scb  extends uvm_scoreboard;

	protected int hmc_rsp_packet_count = 0;
	protected int hmc_req_packet_count = 0;
	protected int hmc_error_response_count = 0;
	protected int axi4_rsp_packet_count = 0;
	protected int axi4_req_packet_count = 0;
	protected int axi4_error_response_count = 0;
	


	typedef hmc_packet hmc_request_queue[$];
	typedef bit [127:0] flit_t;
	hmc_request_queue axi4_np_requests[*];
	hmc_packet axi4_2_hmc[$];
	hmc_packet hmc_response[$];
	hmc_packet axi4_response[$];
	
	
	int valid_cycle = 0;
	
	//--check tags
	int tag_count = 512;
	bit [512:0]used_tags;
	

	//-- analysis imports
	//-- HMC Interface
    `uvm_analysis_imp_decl(_hmc_req)
    uvm_analysis_imp_hmc_req #(hmc_packet, hmc_module_scb) hmc_req_port;
    `uvm_analysis_imp_decl(_hmc_rsp)
    uvm_analysis_imp_hmc_rsp #(hmc_packet, hmc_module_scb) hmc_rsp_port;
	
	//-- Host Interface
    `uvm_analysis_imp_decl(_axi4_hmc_req)
    uvm_analysis_imp_axi4_hmc_req #(hmc_packet, hmc_module_scb	) axi4_hmc_req; 
    `uvm_analysis_imp_decl(_axi4_hmc_rsp)
    uvm_analysis_imp_axi4_hmc_rsp #(hmc_packet, hmc_module_scb	) axi4_hmc_rsp;
    
    
	`uvm_component_utils(hmc_module_scb )

	function new (string name="hmc_module_scb", uvm_component parent);
		super.new(name, parent);
		axi4_hmc_req = new("axi4_hmc_req",this);
		axi4_hmc_rsp = new("axi4_hmc_rsp",this);
		hmc_req_port = new("hmc_req_port",this);
		hmc_rsp_port = new("hmc_rsp_port",this);
	endfunction : new

	//-- compare the received response packets and check with the previous sent request packet
	function void response_compare(input hmc_packet expected, input hmc_packet packet);
		int i;
		hmc_packet request;
		
		if (packet.command != HMC_ERROR_RESPONSE) begin //-- HMC_ERROR_RESPONSE has no label
			//-- Check the packet against the request stored in the axi4_np_requests map
			label : assert (axi4_np_requests.exists(packet.tag))
				else `uvm_fatal(get_type_name(),$psprintf("response_compare: Unexpected Response with tag %0x \n%s", packet.tag, packet.sprint()));
			
			//-- delete the previous sent request packet
			request = axi4_np_requests[packet.tag].pop_front();
			if (axi4_np_requests[packet.tag].size() == 0)
				axi4_np_requests.delete(packet.tag);
		end
		//-- check the hmc_packet
		if (packet.command == HMC_WRITE_RESPONSE 
				&& request.get_command_type() != HMC_WRITE_TYPE 
				&& request.get_command_type() != HMC_MISC_WRITE_TYPE)
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Write Response received with tag %0x for request %s\n%s", packet.tag, request.command.name(), packet.sprint()))

		if (packet.command == HMC_READ_RESPONSE && request.get_command_type() != HMC_READ_TYPE && request.get_command_type() != HMC_MODE_READ_TYPE )
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Read Response received with tag %0x for request %s\n%s", packet.tag, request.command.name(), packet.sprint()))

		if (packet.command == HMC_READ_RESPONSE) begin
			int expected_count;
			case (request.command)
				HMC_MODE_READ: expected_count = 1;
				HMC_READ_16:   expected_count = 1;
				HMC_READ_32:   expected_count = 2;
				HMC_READ_48:   expected_count = 3;
				HMC_READ_64:   expected_count = 4;
				HMC_READ_80:   expected_count = 5;
				HMC_READ_96:   expected_count = 6;
				HMC_READ_112:  expected_count = 7;
				HMC_READ_128:  expected_count = 8;
				default:      expected_count = 0;
			endcase
			if (expected_count != packet.payload.size())
				`uvm_fatal(get_type_name(),$psprintf("response_compare: Read Response received with tag %0x and wrong size req=%0s rsp payload size=%0x\n", packet.tag, request.command.name(), packet.payload.size()))
		end

		//-- Check that the HMC command matches the HTOC item
		if (packet.get_command_type() != HMC_RESPONSE_TYPE)
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Unexpected Packet \n%s", packet.sprint()))

		if (expected.command != packet.command)
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Expected %s, got %s", expected.command.name(), packet.command.name()))

		if (expected.tag != packet.tag) begin
			`uvm_info(get_type_name(), $psprintf("Expected: %s. got: %s", expected.sprint(), packet.sprint() ), UVM_LOW)	
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Packet tag mismatch %0d != %0d ", expected.tag, packet.tag))
		end	

		if (expected.packet_length != packet.packet_length) begin
			`uvm_info(get_type_name(), $psprintf("Expected: %s. got: %s", expected.sprint(), packet.sprint() ), UVM_LOW)	
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Packet length mismatch %0d != %0d ", expected.packet_length, packet.packet_length))
		end
		
		if (expected.payload.size() != packet.payload.size())
			`uvm_fatal(get_type_name(),$psprintf("response_compare: Payload size mismatch %0d != %0d", expected.payload.size(), packet.payload.size()))

		for (int i=0; i<packet.payload.size(); i++) begin
			if (packet.payload[i] != expected.payload[i])
				`uvm_fatal(get_type_name(),$psprintf("response_compare: Payload mismatch at %0d %0x != %0x", i, packet.payload[i], expected.payload[i]))
		end

	endfunction : response_compare

	//-- compare and check 2 Request type packets
	function void request_compare(input hmc_packet expected, hmc_packet packet);

		hmc_command_type packet_type = packet.get_command_type();
		if (packet_type == HMC_FLOW_TYPE || packet_type == HMC_RESPONSE_TYPE)
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Unexpected Packet \n%s", packet.sprint()))

		if (expected.command != packet.command) begin
			`uvm_info(get_type_name(), $psprintf("Expected: %s. got: %s", expected.sprint(), packet.sprint() ), UVM_LOW)	
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Expected %s, got %s", expected.command.name(), packet.command.name()))
		end

		if (expected.cube_ID != packet.cube_ID)
			`uvm_fatal(get_type_name(),$psprintf("request_compare: cube_ID mismatch %0d != %0d", expected.cube_ID, packet.cube_ID))

		if (expected.address != packet.address)
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Address mismatch %0d != %0d", expected.address, packet.address))

		if (expected.packet_length != packet.packet_length)
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Packet length mismatch %0d != %0d", expected.packet_length, packet.packet_length))

		if (expected.tag != packet.tag) begin
			`uvm_info(get_type_name(), $psprintf("Expected: %s. got: %s", expected.sprint(), packet.sprint() ), UVM_LOW)	
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Packet tag mismatch %0d != %0d ", expected.tag, packet.tag))
		end	
		
		if (expected.payload.size() != packet.payload.size())
			`uvm_fatal(get_type_name(),$psprintf("request_compare: Payload size mismatch %0d != %0d", expected.payload.size(), packet.payload.size()))

		for (int i=0;i<expected.payload.size();i = i+1) begin
			if (expected.payload[i] != packet.payload[i])
				`uvm_fatal(get_type_name(),$psprintf("request_compare: Payload mismatch at %0d %0x != %0x", i, expected.payload[i], packet.payload[i]))
		end
	endfunction : request_compare

	function void write_hmc_rsp(input hmc_packet packet);
		hmc_packet expected;

		if (packet.command != HMC_ERROR_RESPONSE) begin //TODO cover error response
			hmc_rsp_packet_count++;
			`uvm_info(get_type_name(),$psprintf("hmc_rsp: received packet #%0d %s", hmc_rsp_packet_count, packet.command.name()), UVM_MEDIUM)
			`uvm_info(get_type_name(),$psprintf("hmc_rsp: \n%s", packet.sprint()), UVM_HIGH)
		end else begin
			hmc_error_response_count++;
			`uvm_info(get_type_name(),$psprintf("hmc_error_rsp: received error response #%0d %s", hmc_error_response_count, packet.command.name()), UVM_MEDIUM)
			`uvm_info(get_type_name(),$psprintf("hmc_error_rsp: \n%s", packet.sprint()), UVM_HIGH)
		end

		//-- check this packet later 
		
		//-- the response packet might be delayed due to the packet mon
		//-- check if the response packet is already received on the axi link
		if (axi4_response.size() == 0)
			hmc_response.push_back(packet);
		else begin //-- check the packet
			expected = axi4_response.pop_front();
			response_compare(expected, packet); //TODO

			if (packet.command != HMC_ERROR_RESPONSE) begin //TODO cover error response
								//-- check if open request with tag is available
				if (used_tags[packet.tag] == 1'b1) begin
					used_tags[packet.tag] =  1'b0;
				end else begin
					`uvm_fatal(get_type_name(),$psprintf("Packet with Tag %0d was not requested", packet.tag))
				end
			end
		end
	endfunction : write_hmc_rsp

	function void write_hmc_req(input hmc_packet packet);
		hmc_packet expected;

		if (packet == null) begin
		  `uvm_fatal(get_type_name(), $psprintf("packet is null"))
		 end
		
		hmc_req_packet_count++;	

		`uvm_info(get_type_name(),$psprintf("hmc_req: received packet #%0d %s@%0x (tok %0d)", hmc_req_packet_count, packet.command.name(), packet.address, packet.return_token_count), UVM_MEDIUM)
		`uvm_info(get_type_name(),$psprintf("hmc_req: \n%s", packet.sprint()), UVM_HIGH)

		//-- expect an request packet on the host (AXI4) request queue
		if (axi4_2_hmc.size() == 0)
			`uvm_fatal(get_type_name(),$psprintf("write_hmc_req: Unexpected packet (the request queue is empty)\n%s",packet.sprint()))
		else
			expected = axi4_2_hmc.pop_front();

		//-- compare and check 2 Request type packets
		request_compare(expected, packet);

		`uvm_info(get_type_name(),$psprintf("hmc_req: checked packet #%0d %s@%0x", hmc_req_packet_count, packet.command.name(), packet.address), UVM_MEDIUM)
	endfunction : write_hmc_req
	
	
	function void write_axi4_hmc_rsp(input hmc_packet packet);
	
		 hmc_packet expected;
		 if (packet == null) begin
		  `uvm_fatal(get_type_name(), $psprintf("packet is null"))
		 end
		 
		 if (packet.command != HMC_ERROR_RESPONSE) begin //TODO cover error response
			axi4_rsp_packet_count++;
			`uvm_info(get_type_name(),$psprintf("axi4_rsp: received packet #%0d %s", axi4_rsp_packet_count, packet.command.name()), UVM_MEDIUM)
			`uvm_info(get_type_name(),$psprintf("axi4_rsp: \n%s", packet.sprint()), UVM_HIGH)
		end else begin
			axi4_error_response_count++;
			`uvm_info(get_type_name(),$psprintf("axi4_error_rsp: received error response #%0d %s", axi4_error_response_count, packet.command.name()), UVM_MEDIUM)
			`uvm_info(get_type_name(),$psprintf("axi4_error_rsp: \n%s", packet.sprint()), UVM_HIGH)
		end

		//-- the response packet might be delayed due to the transmission mon. 
		//-- due to this the compare must be executed later
		
		//-- compare with previous on the HMC side received response packet
		
		if (hmc_response.size()== 0) 
			axi4_response.push_back(packet);
		else begin //-- check
			expected = hmc_response.pop_front();
			response_compare(expected, packet); //TODO

			if (packet.command != HMC_ERROR_RESPONSE) begin //TODO cover error response
				//-- check if open request with tag is available
				if (used_tags[packet.tag] == 1'b1) begin
					used_tags[packet.tag] =  1'b0;
				end else begin
					`uvm_fatal(get_type_name(),$psprintf("Packet with Tag %0d was not requested", packet.tag))
				end
			end
		end
	endfunction :write_axi4_hmc_rsp


	function void write_axi4_hmc_req(input hmc_packet packet);
		if (packet == null) begin
		  `uvm_fatal(get_type_name(), $psprintf("packet is null"))
		end
		`uvm_info(get_type_name(),$psprintf("collected a packet %s", packet.command.name()), UVM_HIGH)
		`uvm_info(get_type_name(),$psprintf("\n%s", packet.sprint()), UVM_HIGH)
		
		//-- check packet later
		axi4_req_packet_count++;
		axi4_2_hmc.push_back(packet);
		
		//-- check if tag checking is necessary
		if (packet.get_command_type() == HMC_WRITE_TYPE 
				|| packet.get_command_type() == HMC_MISC_WRITE_TYPE 
				|| packet.get_command_type() == HMC_READ_TYPE 
				|| packet.get_command_type() == HMC_MODE_READ_TYPE)
		begin
			//-- store this packet to check corresponding response packet later
			if (!axi4_np_requests.exists(packet.tag)) begin
				axi4_np_requests[packet.tag] = {};
			end 
			else begin
				`uvm_info(get_type_name(),$psprintf("There is already an outstanding axi4 request with tag %0x!", packet.tag), UVM_MEDIUM)
			end
			axi4_np_requests[packet.tag].push_back(packet);
				
			if (used_tags[packet.tag] == 1'b0) begin
				used_tags[packet.tag] =  1'b1;
			end else begin
				`uvm_fatal(get_type_name(), $psprintf("tag %0d is already in use", packet.tag))
			
			end
		end
			
		`uvm_info(get_type_name(),$psprintf("axi4_req: received packet #%0d %s@%0x", axi4_req_packet_count, packet.command.name(), packet.address), UVM_MEDIUM)
		`uvm_info(get_type_name(),$psprintf("axi4_req: \n%s", packet.sprint()), UVM_HIGH)
			
	endfunction :write_axi4_hmc_req
	
	function void check_phase(uvm_phase phase);
		
		if (axi4_rsp_packet_count != hmc_rsp_packet_count)
			`uvm_fatal(get_type_name(),$psprintf("axi4_rsp_packet_count = %0d hmc_rsp_packet_count = %0d!", axi4_rsp_packet_count, hmc_rsp_packet_count))
		if (axi4_req_packet_count != hmc_req_packet_count)
			`uvm_fatal(get_type_name(),$psprintf("axi4_req_packet_count = %0d hmc_req_packet_count = %0d!", axi4_req_packet_count, hmc_req_packet_count))
		
		//-- check for open requests on the host side
		if (axi4_np_requests.size() > 0) begin
			for(int i=0;i<512;i++)begin
				if (axi4_np_requests.exists(i))begin
					`uvm_info(get_type_name(),$psprintf("Unanswered Requests: %0d with tag %0d", axi4_np_requests[i].size(), i), UVM_LOW)
				end
			end
			`uvm_fatal(get_type_name(),$psprintf("axi4_np_requests.size() = %0d, not all requests have been answered!", axi4_np_requests.size()))
		end
		
		//-- check for open tags
		if (used_tags >0) begin
			foreach(used_tags[i]) begin
				if (used_tags[i] == 1'b1)
					`uvm_info(get_type_name(),$psprintf("Tag %0d is in use",  i), UVM_LOW)
			end
			`uvm_fatal(get_type_name(),$psprintf("Open Tags!"))
		end
	endfunction : check_phase

	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$psprintf("axi4_req_count %0d", axi4_req_packet_count), UVM_LOW)
		`uvm_info(get_type_name(),$psprintf("axi4_rsp_count %0d", axi4_rsp_packet_count), UVM_LOW)
		`uvm_info(get_type_name(),$psprintf("hmc_req_count %0d",  hmc_req_packet_count),  UVM_LOW)
		`uvm_info(get_type_name(),$psprintf("hmc_rsp_count %0d",  hmc_rsp_packet_count),  UVM_LOW)
		`uvm_info(get_type_name(),$psprintf("Error response count %0d", axi4_error_response_count ),  UVM_LOW)
	endfunction : report_phase

endclass : hmc_module_scb

`endif // HMC_SCOREBOARD_SV
