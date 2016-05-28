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
`ifndef hmc_transaction_mon_sv
`define hmc_transaction_mon_sv

class hmc_transaction_mon extends uvm_monitor;

	hmc_packet	hmc_buffer[$];
	bit [7:0]	last_rrp = 0;
	bit [2:0]	next_sequence_num;
	hmc_tag_mon tag_mon;
	
	uvm_active_passive_enum enable_tag_checking = UVM_ACTIVE;

	`uvm_analysis_imp_decl(_hmc_pkt)
	uvm_analysis_imp_hmc_pkt #(hmc_packet, hmc_transaction_mon) pkt_import;
	`uvm_analysis_imp_decl(_hmc_rrp)
	uvm_analysis_imp_hmc_rrp #(int, hmc_transaction_mon) rrp_import;
	
	

	uvm_analysis_port #(hmc_packet) transaction_finished_port;
	
	`uvm_component_utils_begin(hmc_transaction_mon)
		`uvm_field_enum(uvm_active_passive_enum, enable_tag_checking, UVM_DEFAULT)
	`uvm_component_utils_end
	
	function new ( string name="hmc_transaction_mon", uvm_component parent );
		super.new(name, parent);
		
		pkt_import = new("pkt_import",this);
		rrp_import = new("rrp_import",this);
		
		transaction_finished_port = new("transaction_finished_port", this);
		
		next_sequence_num = 3'b1;

		
		hmc_buffer = {};

		
	endfunction : new
	
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

	endfunction : build_phase


	function void write_hmc_pkt(input hmc_packet collected_packet);
		
		if (collected_packet.command 	!= HMC_NULL 
			&& collected_packet.command	!= HMC_IRTRY
			&& collected_packet.command != HMC_PRET
		) 
		begin
			`uvm_info(get_type_name(),	$psprintf("got packet with command %s and frp %d", collected_packet.command.name(),collected_packet.forward_retry_pointer), UVM_HIGH)
			hmc_buffer.push_back(collected_packet);
		end	
		
		

	endfunction : write_hmc_pkt

	function void tag_handling (hmc_packet packet );
		if (packet.get_command_type() == HMC_WRITE_TYPE 		||
			packet.get_command_type() == HMC_MISC_WRITE_TYPE	||
			packet.get_command_type() == HMC_MODE_READ_TYPE	||
			packet.get_command_type() == HMC_READ_TYPE) 
		begin
			tag_mon.use_tag(packet.tag);
		end
		
		if (packet.get_command_type() 	== HMC_RESPONSE_TYPE &&
						 packet.command != HMC_ERROR_RESPONSE &&
						!packet.poisoned)
		begin
			tag_mon.release_tag(packet.tag);
		end

	endfunction : tag_handling

	
	function void write_hmc_rrp(int rrp);
		if (rrp != last_rrp) begin
			hmc_packet current_packet;
			`uvm_info(get_type_name(),$psprintf("searching packet with FRP %d", rrp),UVM_HIGH)
			if (hmc_buffer.size()>0) begin
				do begin
					if (hmc_buffer.size()>0) begin
						current_packet = hmc_buffer.pop_front();

							if ((current_packet.command != HMC_TRET) ) begin
								`uvm_info(get_type_name(),$psprintf("send packet with command %s and frp %d", current_packet.command.name(),current_packet.forward_retry_pointer), UVM_HIGH)
								if (current_packet.poisoned)
									`uvm_info(get_type_name(), $psprintf("Packet was poisoned"), UVM_NONE)
								else begin
									if(enable_tag_checking == UVM_ACTIVE)
										tag_handling(current_packet);
									transaction_finished_port.write(current_packet);
								end
							end 
					end
					else 
						`uvm_fatal(get_type_name(),$psprintf("Cant find RRP %d in retry buffer", rrp))
				end while (current_packet.forward_retry_pointer != rrp);
			end else 
			`uvm_info(get_type_name(), $psprintf("retry buffer is empty, can not find matching rrp (%0d)", rrp), UVM_HIGH)
			last_rrp = rrp;
		end
	endfunction : write_hmc_rrp

	
	function bit idle_check();
		if (enable_tag_checking == UVM_ACTIVE)
			return hmc_buffer.size()==0 && tag_mon.idle_check();
		else
			return hmc_buffer.size()==0;
	endfunction : idle_check	
	
	function void check_phase(uvm_phase phase);
		hmc_packet pkt;
		
		if (hmc_buffer.size() >0) begin
			`uvm_info(get_type_name(),$psprintf("retry buffer is not empty!"),UVM_NONE)
			while(hmc_buffer.size()>0) begin
				pkt = hmc_buffer.pop_front();
				`uvm_info(get_type_name(),$psprintf("Open FRP: %d", pkt.forward_retry_pointer), UVM_NONE)
			end
			//-- print packet
			`uvm_fatal(get_type_name(),$psprintf("retry buffer is not empty!"))
		end
		
	endfunction : check_phase
	

	
endclass : hmc_transaction_mon

`endif // hmc_transaction_mon_sv