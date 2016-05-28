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

class cag_rgm_repeat_block extends cag_rgm_container;//cag_rgm_base;

	protected int unsigned loop;
	protected bit [63:0] iter_size;
	protected cag_rgm_container containers[$];

	`uvm_object_utils(cag_rgm_repeat_block)
	
	function new(string name = "cag_rgm_repeat_block");
		super.new(name);
		this.name = name;
		this.m_type = REPEAT_BLOCK;
	endfunction : new
	
	function void add_container(cag_rgm_container container);
		container.set_address(address + (loop*iter_size));
		container.set_loop(loop);
		this.containers.push_back(container);
		loop++;
	endfunction : add_container
	
	function void set_iter_size(bit [63:0] iter_size);
		this.iter_size = iter_size;
	endfunction : set_iter_size
	
	virtual function string do_print_rf(string s = "");
		return {s,$psprintf(", loops: %0d, iter_size: %0h",loop,iter_size)};
	endfunction : do_print_rf
	
	virtual function void print_rf(string prefix="");
		super.print_rf(prefix);
		
		foreach(containers[i])
			containers[i].print_rf({prefix,"   "});
	endfunction : print_rf
	
	virtual function cag_rgm_base get_by_name(string full_name = "");
		bit check_registers = 1;
		
		string name;
		
		for( int i = 0; i < full_name.len(); i++) begin
			if(full_name.getc(i) == ".") begin
				name = full_name.substr(0, i-1);
				full_name = full_name.substr(i + 1, full_name.len()-1);
				check_registers = 0;
				break;
			end
		end
		
		if(check_registers) begin
			foreach(containers[i]) begin
				if(containers[i].get_name() == full_name) begin
					return containers[i];
				end
			end
		end else begin		
			foreach(containers[i]) begin
				if(containers[i].get_name() == name) begin
					return containers[i].get_by_name(full_name);
				end
			end
		end
		
		return null;
		
	endfunction : get_by_name
	
	virtual function cag_rgm_base get_by_address(bit [63:0] address);
		foreach(containers[i]) begin
			get_by_address = containers[i].get_by_address(address);
			if( get_by_address != null)
				return get_by_address;				
		end
		return null;
	endfunction : get_by_address
	
endclass : cag_rgm_repeat_block
