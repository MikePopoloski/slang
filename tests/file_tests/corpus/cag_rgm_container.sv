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

class cag_rgm_container extends cag_rgm_base;

	protected cag_rgm_base m_registers[$];
	protected cag_rgm_base m_ramblocks[$];
	
	`uvm_object_utils(cag_rgm_container)
	
	function new(string name = "cag_rgm_container");
		super.new(name);
		this.name = name;
		this.m_type = CONTAINER;
	endfunction : new
	
	function void add_register(cag_rgm_register register, bit set_address = 0);
		if(set_address)
			register.set_address(address);
		m_registers.push_back(register);
	endfunction : add_register
	
	function void add_ramblock(cag_rgm_base ramblock, bit set_address = 0);
		if(set_address)
			ramblock.set_address(address);
		m_ramblocks.push_back(ramblock);
	endfunction : add_ramblock
	
	virtual function void set_address(bit [63:0] address);
		super.set_address(address);
		
		foreach(m_registers[i])
			m_registers[i].set_address(address);
			
		foreach(m_ramblocks[i])
			m_ramblocks[i].set_address(address);
		
	endfunction : set_address
	
	virtual function void set_loop(int loop);
		super.set_loop(loop);
		
		foreach(m_registers[i])
			m_registers[i].set_loop(loop);
			
		foreach(m_ramblocks[i])
			m_ramblocks[i].set_loop(loop);
		
	endfunction : set_loop
	
	virtual function cag_rgm_base get_by_name(string full_name = "");
	
		foreach(m_registers[i]) begin
			if(m_registers[i].get_name() == full_name) begin
				return m_registers[i];
			end
		end
		foreach(m_ramblocks[i]) begin
			if(m_ramblocks[i].get_name() == full_name) begin
				return m_ramblocks[i];
			end
		end
		
		return null;
	endfunction : get_by_name
	
	virtual function cag_rgm_base get_by_address(bit [63:0] address);
		foreach(m_registers[i]) begin
			if(m_registers[i].address_match(address) != -1) begin
				return m_registers[i];
			end
		end
		foreach(m_ramblocks[i]) begin
			if(m_ramblocks[i].address_match(address) != -1) begin
				return m_ramblocks[i];
			end
		end
		
		return null;
	endfunction : get_by_address
	
	virtual function void print_rf(string prefix = "");
		super.print_rf(prefix);
		
		foreach (m_registers[i]) begin
			m_registers[i].print_rf({prefix,"   "});
		end
		
		foreach (m_ramblocks[i]) begin
			m_ramblocks[i].print_rf({prefix,"   "});
		end

	endfunction : print_rf
	
endclass : cag_rgm_container

/******************************************************************************
*
* REVISION HISTORY:
*    
*******************************************************************************/
