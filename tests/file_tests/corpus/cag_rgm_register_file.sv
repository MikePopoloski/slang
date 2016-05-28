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

class cag_rgm_register_file extends cag_rgm_container;

	protected cag_rgm_register_file m_register_files[$];
	protected cag_rgm_repeat_block  m_repeat_blocks[$];
	
	`uvm_object_utils(cag_rgm_register_file)
	
	function new(string name="cag_rgm_register_file");
		super.new(name);
		this.name = name;
		this.m_type = REGISTER_FILE;
	endfunction : new
		
	function void add_register_file(cag_rgm_register_file register_file);
		m_register_files.push_back(register_file);
	endfunction : add_register_file
	
	function void add_repeat_block(cag_rgm_repeat_block repeat_block);
		m_repeat_blocks.push_back(repeat_block);
	endfunction : add_repeat_block
	
	function cag_rgm_base get_by_name(string full_name = "");
		bit check_registers = 1;
		cag_rgm_base base;
		cag_rgm_register_file m_reg_file;
		cag_rgm_repeat_block m_repeat;
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
			base = super.get_by_name(full_name);
			if(base != null)
				return base;
				
			foreach(m_repeat_blocks[i]) begin
				if(m_repeat_blocks[i].get_name() == full_name) begin
					return m_repeat_blocks[i];
				end
			end
		end else begin		
			foreach(m_register_files[i]) begin
				if(m_register_files[i].get_name() == name) begin
					$cast(m_reg_file,m_register_files[i]);
					return m_reg_file.get_by_name(full_name);
				end
			end
			foreach(m_repeat_blocks[i]) begin
				if(m_repeat_blocks[i].get_name() == name) begin
					$cast(m_repeat,m_repeat_blocks[i]);
					return m_repeat_blocks[i].get_by_name(full_name);
				end
			end
		end
				
		return null;
		
	endfunction : get_by_name
	
	virtual function cag_rgm_base get_by_address(bit [63:0] address);
		// check registers and ram blocks
		get_by_address = super.get_by_address(address);
		if(get_by_address != null)
			return get_by_address;

		// check sub registerfiles			
		foreach(m_register_files[i]) begin
			get_by_address = m_register_files[i].get_by_address(address);
			if(get_by_address != null)
				return get_by_address;
		end
		
		// check repeat blocks
		foreach(m_repeat_blocks[i]) begin
			get_by_address = m_repeat_blocks[i].get_by_address(address);
			if(get_by_address != null)
				return get_by_address;
		end
		
		return null;
	endfunction : get_by_address
	
	virtual function void print_rf(string prefix = "");
		super.print_rf(prefix);
		
		foreach(m_register_files[i])
			m_register_files[i].print_rf({prefix,"   "});
			
		foreach(m_repeat_blocks[i])
			m_repeat_blocks[i].print_rf({prefix,"   "});
	endfunction : print_rf
	
endclass : cag_rgm_register_file

/******************************************************************************
*
* REVISION HISTORY:
*    
*******************************************************************************/
