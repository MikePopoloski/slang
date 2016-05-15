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
// tag handler 
//
//

`ifndef TAG_HANDLER_SV
`define TAG_HANDLER_SV

class tag_handler  extends uvm_component;

	int tag_count = 512;		//-- tags available at the beginning
	bit tags_in_use[];		//-- bitmap of current used tags
	int tag_fifo[$];
	int transaction_count;
	int max_tags_in_use;
	int num_tags_in_use;
	int used_tag;

    event tag_avail_event;
	
	covergroup tags_used_cg;
		TAGS_USED : coverpoint used_tag{
			bins valid_tags [] = {[0:tag_count-1]};
			bins illegal_tags = {[tag_count:$]};
			}
	endgroup

    `uvm_analysis_imp_decl(_hmc_rsp)
    uvm_analysis_imp_hmc_rsp #(hmc_packet, tag_handler) hmc_rsp_port;

	`uvm_component_utils_begin(tag_handler)
		`uvm_field_int(tag_count, UVM_DEFAULT)
	`uvm_component_utils_end

	function new ( string name="tag_handler", uvm_component parent );
		super.new(name, parent);
		tags_used_cg = new(); 
	endfunction : new
	
	function void build_phase(uvm_phase phase);
		hmc_rsp_port = new("hmc_rsp_port",this);
		
		tags_in_use = new [tag_count];

		max_tags_in_use = 0;
		transaction_count = 0;
		reset();
	endfunction : build_phase

	function void reset();
		
		foreach (tags_in_use[i]) begin
			tags_in_use[i] =0;
		end

		num_tags_in_use = 0;
		tag_fifo = {};
		
		for (int i=0; i< tag_count; i++) 
			tag_fifo.push_back(tag_count-1-i);
	endfunction : reset

	task get_tag(ref int tag );
		//-- wait until at least 1 tag available
		if (tag_fifo.size() == 0) begin
			`uvm_info(get_type_name(), $psprintf("get_tag: no tags available...waiting"), UVM_HIGH)
			@(tag_avail_event);
			`uvm_info(get_type_name(), $psprintf("get_tag: one tag is now available"), UVM_HIGH)
		end
		
		//-- flag tag as used
		tag = tag_fifo.pop_front();
		tags_in_use[tag] = 1'b1;
		used_tag = tag;
		tags_used_cg.sample();
		
		num_tags_in_use++;
		if (num_tags_in_use > max_tags_in_use)
			max_tags_in_use = num_tags_in_use;
	endtask : get_tag
	
		task try_get_tag(ref int tag );
		//-- wait until at least 1 tag available
		if (tag_fifo.size() == 0) begin
			`uvm_info(get_type_name(), $psprintf("get_tag: no tags available...returning NULL"), UVM_HIGH)
			tag = -1;
		end else begin
		
			//-- flag tag as used
			tag = tag_fifo.pop_front();
			tags_in_use[tag] = 1'b1;
			used_tag = tag;
			tags_used_cg.sample();
		
			num_tags_in_use++;
			if (num_tags_in_use > max_tags_in_use)
				max_tags_in_use = num_tags_in_use;
		end
	endtask : try_get_tag

	function void release_tag(input int tag);
		if (!tags_in_use[tag])
			`uvm_fatal(get_type_name(), $psprintf("release_tag: tag (%0d) not in use!", tag))
		//-- release tag
		tags_in_use[tag] = 1'b0;
		num_tags_in_use--;
		transaction_count++;
		tag_fifo.push_back(tag);

		//-- signal that tag is available
		-> tag_avail_event;
	endfunction : release_tag

	function void write_hmc_rsp(input hmc_packet packet);
		if (packet.command != HMC_ERROR_RESPONSE)
			release_tag(packet.tag);
	endfunction : write_hmc_rsp

	function void idle_check();
		if (num_tags_in_use > 0)
			for (int i=0; i<tag_count; i++)
				if (tags_in_use[i])
					`uvm_fatal(get_type_name(), $psprintf("%0d tags still in use, first one is %0d!", num_tags_in_use, i))
		if (tag_fifo.size() != tag_count)
			`uvm_fatal(get_type_name(), $psprintf("tag FIFO should have num_tags (%0d) entries it has %0d!", tag_count, tag_fifo.size()))
	endfunction : idle_check

	function void check_phase(uvm_phase phase);
		idle_check();
	endfunction : check_phase

	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$psprintf("max_tags_in_use %0d, transaction_count %0d", max_tags_in_use, transaction_count), UVM_LOW)
	endfunction : report_phase

endclass : tag_handler

`endif // TAG_HANDLER_SV
