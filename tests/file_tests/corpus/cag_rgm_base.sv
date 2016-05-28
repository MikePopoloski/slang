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

class cag_rgm_base extends uvm_object;

	protected CAG_RGM_TYPE m_type = NONE;
	protected bit [63:0] address;
	protected bit [63:0] offset;
	protected int loop = -1;
	protected string name;
	protected bit check_on_read = 1;

	`uvm_object_utils_begin(cag_rgm_base)
	`uvm_field_int(address, UVM_NOCOMPARE | UVM_NOPACK | UVM_DEFAULT)
	`uvm_field_int(offset, UVM_NOCOMPARE | UVM_NOPACK | UVM_DEFAULT)
	`uvm_field_int(check_on_read, UVM_NOCOMPARE | UVM_NOPACK | UVM_DEFAULT) 
	`uvm_field_string(name, UVM_NOCOMPARE | UVM_NOPACK | UVM_DEFAULT)
	`uvm_object_utils_end

	function new(string name="cag_rgm_base");
		super.new(name);
	endfunction : new

	function CAG_RGM_TYPE get_rgm_type();
		return m_type;
	endfunction : get_rgm_type

	function string get_name();
		return name;
	endfunction : get_name

	function void set_name(string name);
		this.name = name;
	endfunction : set_name

	virtual function void set_address(bit [63:0] address);
		this.address = address;
	endfunction : set_address

	virtual function bit [63:0] get_address();
		return address + offset;
	endfunction : get_address

	virtual function int address_match(bit [63:0] address);
		if(get_address() == address)
			return 1;
		else
			return -1;
	endfunction : address_match

	function void set_offset(bit [63:0] offset);
		this.offset = offset;
	endfunction : set_offset

	function bit [63:0] get_offset();
		return offset;
	endfunction : get_offset

	virtual function void set_loop(int loop);
		this.loop = loop;
	endfunction : set_loop

	function int get_loop();
		return loop;
	endfunction : get_loop

	function void set_check_on_read(bit check_on_read);
		this.check_on_read = check_on_read;
	endfunction : set_check_on_read

	function bit get_check_on_read();
		return this.check_on_read;
	endfunction : get_check_on_read 

	function void set_raw(bit [63:0] data, bit endian = 1);
		bit bitstream[];
		int bits;

		bits = pack(bitstream);
		if (endian == 1) begin
			for(int i = 0, int j = bits-1; i < bits; i++, j--)
				bitstream[i] = data[j];
		end else begin
			for(int i = 0; i < bits; i++)
				bitstream[i] = data[i];
		end
		bits = unpack(bitstream);

	endfunction : set_raw

	function bit [63:0] get_raw(bit endian = 1);
		uvm_packer packer = new();
		int bits;
		bit bitstream[];
		bit [63:0] data = 0;

		packer.big_endian = endian;

		bits = pack(bitstream,packer);
		for(int i = 0; i < bits; i++)
			data[i] = bitstream[i];

		return data;
	endfunction

	virtual function void print_rf(string prefix = "");
		$display(do_print_rf($psprintf("%stype: %s, name: %s, address: %0h, offset: %0h",prefix,m_type.name,name,address,offset)));
	endfunction : print_rf

	virtual function string do_print_rf(string s = "");
		return s;
	endfunction : do_print_rf

endclass : cag_rgm_base

/******************************************************************************
	*
	* REVISION HISTORY:
	*    
*******************************************************************************/
