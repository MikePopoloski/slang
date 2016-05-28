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
// hmc link tag checker
//
//

`ifndef hmc_tag_mon_SV
`define hmc_tag_mon_SV

class hmc_tag_mon  extends uvm_component;


	int tags_in_use[int];
	int current_tag;
	int transaction_count;
	int max_tags_in_use;
	
	int max_tags_available = 512;
	
	
	covergroup tags_cg;
		option.per_instance = 1;
		TAGS_IN_USE : coverpoint tags_in_use.size(){
			bins low_usage[]	= {[1:20]};
			bins medium_usage[]	= {[21:250]};
			bins high_usage[]	= {[251:511]};
			bins no_tags_available = {512};
		}
		
		USED_TAGS	: coverpoint current_tag{
			bins TAGS[] = {[1:511]};
		}
	endgroup
	
	`uvm_component_utils_begin(hmc_tag_mon)
		`uvm_field_int(max_tags_available, UVM_DEFAULT)
	`uvm_component_utils_end


	function new ( string name="hmc_tag_mon", uvm_component parent );
		super.new(name, parent);
		tags_in_use.delete();
		max_tags_in_use = 0;
		transaction_count = 0;
		tags_cg = new();
	endfunction : new

	function void reset();
		tags_in_use.delete();
	endfunction : reset

	function void use_tag(input bit [8:0] tag);
		int tmp[];
		
		if (tag > max_tags_available-1)
			`uvm_fatal(get_type_name(), $psprintf("use_tag: tag (%0d) out of range!", tag))
		
		 if(!tags_in_use.exists(tag) ) begin
			tags_in_use[tag] = tag;
			current_tag = tag;
			tags_cg.sample();
		end
	
	endfunction : use_tag

	function void release_tag(input bit [8:0] tag);
		if (tags_in_use.exists(tag))
			tags_in_use.delete(tag);
		else
			`uvm_fatal(get_type_name(), $psprintf("release_tag: tag (%0d) not in use!", tag))

		transaction_count++;
	endfunction : release_tag

	function bit idle_check();
		idle_check = 1;
		if (tags_in_use.size() > 0) begin
			foreach (tags_in_use[i])
				`uvm_info(get_type_name(), $psprintf("%0d tags still in use, Tag %0d is in use!", tags_in_use.size(), i),UVM_LOW)
			idle_check = 0;
		end
	endfunction : idle_check

	function void check_phase(uvm_phase phase);
		if (!idle_check())
			`uvm_fatal(get_type_name(),$psprintf("Tags are still in use"))
	endfunction : check_phase

	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$psprintf("max_tags_in_use %0d, transaction_count %0d", max_tags_in_use, transaction_count), UVM_LOW)
	endfunction : report_phase

endclass : hmc_tag_mon

`endif // hmc_tag_mon_SV
