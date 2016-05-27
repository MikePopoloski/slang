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

`ifndef BFM_2_HMC
`define BFM_2_HMC
class bfm_2_hmc_mon extends hmc_module_mon;
	
	typedef enum {
	 LENGTH_ERROR,
	 CRC_ERROR,
	 SEQ_ERROR,
	 POISON
	}error_class_e;

	mailbox#(cls_pkt) in_mb;
	cls_pkt pkt;
	
	bit [2:0] seq_number = 0;
	
	bit bitstream[];
	
	int phit_size = 64;
	bit [64:0] header;	//-- phit size
	bit [64:0] tail  ;	//-- phit size
	int data_phit_count;
	
	int flit_size = 128;
	
	bit error_abort_mode = 0;
	int irtry_cnt = 0;
	
	int irtry = 0;
	
	
	hmc_link_config link_cfg;
	
	error_class_e current_error;
	hmc_command_encoding current_command;


	int lng_error = 0;
	int crc_error = 0;
	int seq_error = 0;
	int poisoned_pkt =0;
	
	int rsp_rcvd = 0;
	int err_rsp_rcvd = 0;
	int req_rcvd = 0;
	
	hmc_link_config hmc_link_cfg;
	
	`uvm_component_utils_begin(bfm_2_hmc_mon)
		`uvm_field_object(link_cfg, UVM_DEFAULT)
	`uvm_component_utils_end
		covergroup hmc_pkt_error_cg;
		option.per_instance = 1;
		ERROR_TYPE: coverpoint current_error;

		HMC_COMMAND: coverpoint current_command {
			//bins request_commands[] =
			bins flow_types[] = {
				HMC_TRET,
				HMC_PRET,
				HMC_NULL
			};
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
		CROSS_ERROR_TYPPE_COMMAND : cross ERROR_TYPE, HMC_COMMAND;
		
	endgroup
	
	function new ( string name="bfm_2_hmc_mon", uvm_component parent );
		super.new(name, parent);
		hmc_pkt_cg = new();
		hmc_pkt_error_cg = new();
	endfunction : new
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		if (!uvm_config_db#(hmc_link_config)::get(this, "", "link_cfg", link_cfg)) begin
			uvm_report_fatal(get_type_name(), $psprintf("hmc_link_config not set via config_db"));
		end
	endfunction : build_phase
	
	task run();
		cls_pkt old_pkt;
		`uvm_info(get_type_name(),$psprintf("starting BFM_2_HMC converter"), UVM_MEDIUM)
		forever begin
			//mb_pkt.get(pkt);
			old_pkt = pkt;
			in_mb.peek(pkt);
			if (pkt != old_pkt)
				extract_hmc_pkt(pkt);
			else
				#5;
		end
		
	endtask
	
	task extract_hmc_pkt(cls_pkt pkt);
		header				= pkt.get_header();
		tail 				= pkt.get_tail();
		data_phit_count 	= pkt.data.size(); //-- 7 flits->14 phits --> 14-2 =12 data_phits

		bitstream 			= new [2*phit_size + data_phit_count*phit_size];

		//-- generate Bitstream

		if (header !=64'b0) begin

			//-- check length
			if( (header[10:7] != header[14:11]) || (header[10:7] != 1+data_phit_count /2)) begin
				lng_error ++;
				error_abort_mode = 1;
				`uvm_info(get_type_name(),$psprintf("Set error abort mode: LNG/DLN ERROR, Command with header: %h", header), UVM_NONE)
				irtry_cnt = 0;
				
				
				current_error = LENGTH_ERROR;
				current_command[5:0] = header[5:0];
				hmc_pkt_error_cg.sample();
			end else begin
				
				//-- convert the cls_pkt pkt to hmc_packet packet
				cls_pkt_to_hmc_packet(pkt);

				//-- check crc error
				check_crc_error(packet);


				//-- wait for irtry
				if (error_abort_mode)
					clear_error_abort_mode();
	
				else begin

					//-- count Start Error Mode IRTRY
					if (packet.start_retry) begin
						irtry++;
						`uvm_info(get_type_name(),$psprintf("Start Retry: %0d", irtry), UVM_HIGH)
					end

					//-- packet sequence check
					if ((packet.command == HMC_TRET) || (packet.get_command_type() != HMC_FLOW_TYPE))  begin
						irtry = 0; //-- reset start retry mode counter
						
						if (packet.sequence_number != seq_number+1'b1) begin
							seq_error ++;
							error_abort_mode = 1;
							`uvm_info(get_type_name(),$psprintf("Set error abort mode: SEQ ERROR, Command: %s", packet.command.name()), UVM_NONE)
							irtry_cnt = 0;


							//-- sample seq error
							current_error = SEQ_ERROR;
							current_command = packet.command;
							hmc_pkt_error_cg.sample();

						end else begin

							seq_number = packet.sequence_number;

							//-- check if poisoned
							if ( packet.poisoned) begin
								poisoned_pkt++;

								//-- sample poison
								current_error = POISON;
								current_command = packet.command;
								hmc_pkt_error_cg.sample();
							end else
								if((packet.get_command_type() != HMC_FLOW_TYPE))
									write_packet(packet);
						end
					end
				end
			end
		end
		
	endtask : extract_hmc_pkt
	
	
	
	function void check_crc_error(hmc_packet packet);
		if (packet.crc_error) begin
			crc_error++;
			error_abort_mode = 1;
			`uvm_info(get_type_name(),$psprintf("Set error abort mode: CRC ERROR, Command: %s", packet.command.name()), UVM_NONE)
			irtry_cnt = 0;
			
			current_error = CRC_ERROR;
			current_command = packet.command;
			hmc_pkt_error_cg.sample();
		end
	endfunction : check_crc_error
	
	function void clear_error_abort_mode();
		if ((packet.clear_error_abort)) begin
			`uvm_info(get_type_name(), $psprintf("Clear Error Abort Mode: %0d",irtry_cnt ), UVM_HIGH)
			irtry_cnt ++;
		end else begin 
			irtry_cnt = 0;							//-- reset counter
		end 
		
		if (irtry_cnt >= link_cfg.cfg_init_retry_rxcnt) begin			//-- test threshold
			error_abort_mode = 0;
			`uvm_info(get_type_name(), $psprintf("Clear Error Abort Mode" ), UVM_NONE)
		end
	endfunction : clear_error_abort_mode


	function void cls_pkt_to_hmc_packet (cls_pkt pkt);
		//-- Convert the CLS_PKT to HMC_PKT
				for (int b = 0; b < 64; b++) begin								//-- read header to bitmap
					bitstream[b]=header[b];
				end

				if (data_phit_count > 0)
					for (int phit = 0; phit < data_phit_count; phit++)			//-- read data to bitmap
						for (int b = 0; b < phit_size; b++)
							bitstream[(phit + 1) * phit_size + b] = pkt.data[phit][b];
			
				for (int b = 0; b < 64; b++) begin								//-- read tail to bitmap
					bitstream[(data_phit_count+1)*phit_size+b]=tail[b];
				end
				
				//-- create hmc packet
				`uvm_info(get_type_name(),$psprintf("Got a BFM Packet:  %s",pkt.convert2string()), UVM_HIGH)
				packet = hmc_packet::type_id::create("packet", this);
				void'(packet.unpack(bitstream));
		
	endfunction	:	cls_pkt_to_hmc_packet

	task write_packet(hmc_packet packet);
		
		if(packet.get_command_type() == HMC_RESPONSE_TYPE)begin
			if(packet.command != HMC_ERROR_RESPONSE) begin
				`uvm_info(get_type_name(),$psprintf("Rsp #%0d : %s",rsp_rcvd, packet.command.name()), UVM_HIGH)
				`uvm_info(get_type_name(),$psprintf("Rsp #%0d : %s",rsp_rcvd, packet.sprint()), UVM_HIGH)
				rsp_rcvd++;
			end else begin
				`uvm_info(get_type_name(),$psprintf("Err Rsp %0d : %s with error code %b",err_rsp_rcvd, packet.command.name(), packet.error_status), UVM_HIGH)
				err_rsp_rcvd++;				
			end
		end else begin
			`uvm_info(get_type_name(),$psprintf("Req %0d : %s",req_rcvd, packet.command.name()), UVM_HIGH)
			req_rcvd++;
		end


		hmc_pkt_cg.sample();

		item_collected_port.write(packet);
		
	endtask : write_packet
	
	
	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$psprintf("LNG error count  %0d", lng_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("CRC error count  %0d", crc_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("SEQ error count  %0d", seq_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("poisoned packets %0d", poisoned_pkt),	UVM_NONE)
	endfunction : report_phase

endclass


`endif
