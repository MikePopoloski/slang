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
`ifndef HMC_RETRY_BUFFER_SV
`define HMC_RETRY_BUFFER_SV

class hmc_retry_buffer extends uvm_component;

	hmc_packet retry_buffer[$];
	hmc_packet retry_packets[$];
	
	int retry_pos = 0;

	bit [7:0] last_rrp = 8'h0;
	bit [7:0] retry_pointer_head = 8'h0;
	bit [7:0] retry_pointer_next = 8'h0;
	bit retry_in_progress = 0;
	int buffer_usage = 0;

	`uvm_analysis_imp_decl(_return_pointer)
	uvm_analysis_imp_return_pointer#(int, hmc_retry_buffer) return_pointer_imp;

	`uvm_component_utils(hmc_retry_buffer)

	function new(string name="hmc_retry_buffer", uvm_component parent);
		super.new(name,parent);

		return_pointer_imp = new ("return_pointer_imp",this);
		retry_pointer_head = 8'h0;
		retry_pointer_next = 8'h0;
		retry_in_progress = 0;
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

	endfunction : build_phase

	function void reset();
		retry_buffer = {};
		retry_packets = {};
		retry_pointer_head = 8'h0;
		retry_pointer_next = 8'h0;
		retry_in_progress = 0;
	endfunction : reset

	function void write_return_pointer(input int rrp);

		int index = -1;
		`uvm_info(get_type_name(),$psprintf("write_return_pointer: rrp %0d", rrp), UVM_HIGH)
		
		if(last_rrp == rrp)
			return;
		
		last_rrp = rrp;

		for (int i=0; i<retry_buffer.size(); i++) begin
			buffer_usage = buffer_usage - retry_buffer[i].packet_length;
			if (retry_buffer[i].forward_retry_pointer == rrp) begin
				index = i;
				break;
			end
		end

		valid_rrp_found_in_retry_buffer : assert (index!=-1 && index<retry_buffer.size());

		// Delete everything up to the index
		if (retry_buffer.size()-1 == index) begin
			retry_buffer = {};
		end else begin
			retry_buffer = retry_buffer[index+1:$];
		end
	endfunction : write_return_pointer

	function int add_packet(input hmc_packet pkt);
		hmc_packet copy;


		bit [8:0] retry_pointer_next_sum = retry_pointer_next + pkt.packet_length;

		no_add_packet_when_retry_in_progress : assert (retry_in_progress == 0);

		if(retry_pointer_next_sum[7:0] >= last_rrp && retry_pointer_next_sum[8]) begin
			`uvm_info(get_type_name(),$psprintf("add_packet: Retry Buffer full 1 with last frp %0d", last_rrp), UVM_HIGH)
			return -1;
		end

		if(retry_pointer_next_sum >= last_rrp && retry_pointer_next < last_rrp) begin
			`uvm_info(get_type_name(),$psprintf("add_packet: Retry Buffer full 2 with last frp %0d", last_rrp), UVM_HIGH)
			return -1;
		end
		retry_pointer_next = retry_pointer_next_sum[7:0];
		pkt.forward_retry_pointer = retry_pointer_next;
		buffer_usage += pkt.packet_length;

		`uvm_info(get_type_name(),$psprintf("add_packet: %s frp %0d", pkt.command.name(), pkt.forward_retry_pointer), UVM_HIGH)

		copy = new pkt;
		retry_buffer.push_back(copy);
		return retry_pointer_next;
	endfunction : add_packet

	function hmc_packet get_retry_packet();
		if (retry_in_progress == 0 && retry_buffer.size() > 0) begin
			retry_in_progress = 1;
			retry_packets = retry_buffer;
			`uvm_info(get_type_name(),$psprintf("get_retry_packet: start retry with %0d packets", retry_buffer.size()), UVM_HIGH)
			retry_pos = 0;
		end

		if (retry_pos <retry_packets.size()) begin
			retry_pos ++;
			return retry_packets[retry_pos-1];
		end else begin
			retry_in_progress = 0;
			return null;
		end
	endfunction : get_retry_packet

	function void check_phase(uvm_phase phase);
		no_retry_at_check : assert (retry_in_progress == 0);
		if (retry_buffer.size() > 0) begin
			for (int i=0;i<retry_buffer.size();i++) begin
				`uvm_info(get_type_name(),$psprintf("retry_buffer %0d: %s frp %0d", i, retry_buffer[i].command.name(), retry_buffer[i].forward_retry_pointer), UVM_LOW)
			end
		end
		retry_buffer_empty : assert (retry_buffer.size() == 0);
	endfunction : check_phase

	function int get_buffer_used();
		return buffer_usage;
	endfunction : get_buffer_used

endclass : hmc_retry_buffer

`endif // HMC_RETRY_BUFFER_SV
