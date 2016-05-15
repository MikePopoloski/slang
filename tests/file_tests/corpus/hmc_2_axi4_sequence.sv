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
//
// hmc_2_axi4_sequence
//
//

`ifndef HMC_2_AXI4_SEQUENCE_SV
`define HMC_2_AXI4_SEQUENCE_SV

class hmc_2_axi4_sequence #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends uvm_sequence #(axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)));

	int unsigned num_packets = 1;				//-- packets to generate
	int unsigned max_pkts_per_cycle = 4;		//-- maximum packets in single AXI4 cycle
	

	rand hmc_req_packet hmc_items[];
	hmc_packet hmc_packets_ready[$];
	
	int working_pos = 0;
	
	
	typedef bit [1+1+1+127:0] tail_header_flit_t;
	tail_header_flit_t flit_queue[$];
	rand int tag = 0;
	
	constraint tag_value_c {
		tag >= 0;
		tag <  512;
	}

	axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES),.TUSER_WIDTH(TUSER_WIDTH)) axi4_queue[$];

	`uvm_object_param_utils_begin(hmc_2_axi4_sequence #(.DATA_BYTES(DATA_BYTES),.TUSER_WIDTH(TUSER_WIDTH)))
		`uvm_field_int(num_packets, UVM_DEFAULT | UVM_DEC)
		`uvm_field_int(max_pkts_per_cycle, UVM_DEFAULT | UVM_DEC)
	`uvm_object_utils_end

	`uvm_declare_p_sequencer(hmc_2_axi4_sequencer #(.DATA_BYTES(DATA_BYTES),.TUSER_WIDTH(TUSER_WIDTH)))
	

	function new(string name="hmc_2_axi4_sequence");
		super.new(name);

	endfunction : new

	function void pre_randomize ();
		super.pre_randomize();

   		hmc_items = new[num_packets];
			
		foreach (hmc_items[i]) begin
  			hmc_items[i] = hmc_req_packet::type_id::create($psprintf("hmc_item[%0d]", i) );
		end	

  		`uvm_info(get_type_name(),$psprintf("%0d HMC packets generated", num_packets), UVM_HIGH)	
	endfunction : pre_randomize
	
	function void pack_hmc_packet(hmc_packet pkt);
		bit bitstream[];
		tail_header_flit_t tmp_flit;

		int unsigned bitcount;
		int unsigned packet_count=1;

		bitcount = pkt.pack(bitstream);

		pkt_successfully_packed : assert (bitcount > 0);

		//-- For each FLIT in the packet, add the flit entry
		for (int f=0; f<bitcount/128; f++) begin
			for (int i=0; i< 128; i++)
				tmp_flit[i] = bitstream[f*128+i];

			tmp_flit[128] = (f==0); 				//-- Header

			tmp_flit[129] = (f==bitcount/128-1); 	//-- Tail
			
			tmp_flit[130] = 1'b1; 					//-- Flit is valid			

			flit_queue.push_back(tmp_flit);
		end
	endfunction : pack_hmc_packet
	
 	function void hmc_packet_2_axi_cycles();
 	
		axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES),.TUSER_WIDTH(TUSER_WIDTH)) axi4_item;
			
		int unsigned FPW     = DATA_BYTES/16; //--FPW: desired Data width in Flits (HMC packet length) valid: 4.6.8  databytes= tdata_width /8 fpw = tdata_width /128
		int unsigned HEADERS = 1*FPW;
		int unsigned TAILS   = 2*FPW;
		int unsigned VALIDS  = 0;
	 	
	 	int unsigned pkts_in_cycle = 0;		//-- HMC tails inserted in current AXI4 cycle
	 	int unsigned header_in_cycle = 0;		//-- HMC headers inserted in current AXI4 cycle
	 	int unsigned valids_in_cycle = 0;
		hmc_packet hmc_pkt;


		int flit_offset=0;		//-- flit offset First flit-> create new axi_item
		tail_header_flit_t current_flit;
	 	tail_header_flit_t next_flit;
	 	
	 	
		//-- create empty vc
		`uvm_create_on(axi4_item, p_sequencer)
			axi4_item.tdata = 0;
			axi4_item.tuser = 0;
			axi4_item.delay = hmc_packets_ready[0].flit_delay / FPW; //-- measured in flits
		
		while (hmc_packets_ready.size() >0 )  begin		
			hmc_pkt = hmc_packets_ready.pop_front();	
			pack_hmc_packet(hmc_pkt);
			
			
			//-- write flits 2 axi4_queue
			while( flit_queue.size > 0 ) begin 	//-- flit queue contains flits
				
				
				current_flit = flit_queue.pop_front();
				
					if (current_flit[128]) begin 	//-- If current flit is header
						flit_offset += hmc_pkt.flit_delay;
					end
				
				//-- check if axi4_item is full
				if ((flit_offset >= FPW) || pkts_in_cycle == max_pkts_per_cycle  ) begin 
					//-- push full axi item to axi4_queue
					`uvm_info(get_type_name(),$psprintf("axi4_item is full (offset = %0d), writing element %0d to queue ", flit_offset, axi4_queue.size()), UVM_MEDIUM)
					
					if (valids_in_cycle != 0)
					axi4_queue.push_back(axi4_item);
					
					//-- create new AXI4 cycle
					`uvm_create_on(axi4_item, p_sequencer)
					axi4_item.tdata = 0;
					axi4_item.tuser = 0;
					
					//-- set AXI4 cycle delay
					axi4_item.delay = (flit_offset / FPW) -1;	//-- flit offset contains also empty flits
					if (flit_offset % FPW >0)
						axi4_item.delay += 1;
					
					//-- reset counter
					`uvm_info(get_type_name(),$psprintf("HMC Packets in last cycle: %0d, %0d", pkts_in_cycle, header_in_cycle), UVM_HIGH)
					pkts_in_cycle 	= 0;	//-- reset HMC packet counter in AXI4 Cycle
					header_in_cycle = 0;
					valids_in_cycle = 0;
					`uvm_info(get_type_name(),$psprintf("axi_delay is %0d", axi4_item.delay), UVM_MEDIUM)
					
					//-- reset flit_offset
					flit_offset = 0;
				end

				//-- write flit to axi4_item
				for (int i =0;i<128;i++) begin
					axi4_item.tdata[(flit_offset*128)+i] = current_flit[i];
				end
				
				//-- Write tuser flags
				//-- write valid
				axi4_item.tuser[VALIDS	+flit_offset] = current_flit[130];	//-- valid [fpw-1:0]
				//-- write header
				axi4_item.tuser[HEADERS	+flit_offset] = current_flit[128]; 	//-- only 1 if header
				//-- write tail
				axi4_item.tuser[TAILS	+flit_offset] = current_flit[129];	//-- only 1 if tail
				
				valids_in_cycle ++;
				
				
				if(current_flit[129]) begin		//-- count tails in current cycle
					pkts_in_cycle ++;
				end
				
				if(current_flit[128]) begin		//-- count headers in current cycle
					header_in_cycle ++;
				end
				
				//-- debugging output
				if(current_flit[128]) begin
					`uvm_info(get_type_name(),$psprintf("FLIT is header at pos %d", flit_offset), UVM_MEDIUM)
				end
				if(current_flit[129]) begin
					`uvm_info(get_type_name(),$psprintf("FLIT is tail at pos %d", flit_offset), UVM_MEDIUM)
				end
				
				flit_offset++;
			end
		end
		//-- push last axi4_item to axi4_queue
		axi4_queue.push_back(axi4_item);
	
 	endfunction : hmc_packet_2_axi_cycles
	
	
	task aquire_tags();
		for (int i = working_pos; i < hmc_items.size(); i++) begin //-- get a tag for each packet
				//-- only register a tag if response required! 
				if 	(hmc_items[i].get_command_type() == HMC_WRITE_TYPE		||
					 hmc_items[i].get_command_type() == HMC_MISC_WRITE_TYPE ||
					 hmc_items[i].get_command_type() == HMC_READ_TYPE 		||
					 hmc_items[i].get_command_type() == HMC_MODE_READ_TYPE)
				begin
					p_sequencer.handler.get_tag(tag);
				end else begin
					tag = 0;
				end
				
				hmc_items[i].tag = tag;
				
				//-- move packet to ready queue if tag valid
				if (tag >= 0) begin
					
					`uvm_info(get_type_name(),$psprintf("Tag for HMC Packet Type %0d is: %0d", hmc_items[i].get_command_type(), hmc_items[i]), UVM_HIGH)
					hmc_packets_ready.push_back(hmc_items[i]);
					working_pos = i+1;
				end else begin
					break;	//-- send all already processed AXI4 Cycles if tag_handler can not provide an additional tag
				end
			end
		
	endtask : aquire_tags
		
	task send_axi4_cycles();
		axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES),.TUSER_WIDTH(TUSER_WIDTH)) axi4_item;
		while( axi4_queue.size() > 0 ) begin
					`uvm_info(get_type_name(),$psprintf("axi4_queue contains %0d items", axi4_queue.size()), UVM_MEDIUM)
			
					axi4_item = axi4_queue.pop_front();
					
					if ((axi4_item.tuser == {{(TUSER_WIDTH){1'b0}}})) begin
						axi4_item.print();
						`uvm_fatal("AXI4_Master_Driver", "sent an empty cycle")
					end
					`uvm_send(axi4_item);
			
					`uvm_info(get_type_name(),$psprintf("\n%s", axi4_item.sprint()), UVM_HIGH)
				end
		
		
	endtask : send_axi4_cycles
	
	task body();		
		
		`uvm_info(get_type_name(),$psprintf("HMC Packets to send: %0d", hmc_items.size()), UVM_MEDIUM)

		while (hmc_items.size-1 >= working_pos)begin //-- cycle until all hmc_packets have been sent
			//-- try to aquire a tag for each non posted packet
			aquire_tags();

			//-- send all packets with tags
			if (hmc_packets_ready.size()>0) begin

				//-- generate axi4_queue
				hmc_packet_2_axi_cycles();

				//-- send axi4_queue
				send_axi4_cycles();
			end 
		end
	endtask : body

endclass : hmc_2_axi4_sequence

`endif // HMC_2_AXI4_SEQUENCE_SV

