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

class cag_rgm_sequence extends uvm_sequence #(cag_rgm_transfer);

	//`uvm_sequence_utils(cag_rgm_sequence, cag_rgm_sequencer)
	`uvm_object_utils(cag_rgm_sequence)
	`uvm_declare_p_sequencer(cag_rgm_sequencer)

	function new(string name="cag_rgm_sequence");
		super.new(name);
	endfunction : new

	virtual task pre_body();
		uvm_test_done.raise_objection(p_sequencer);
	endtask : pre_body

	virtual task post_body();
		uvm_test_done.drop_objection(p_sequencer);
	endtask : post_body

	function cag_rgm_base get_by_name(string name = "");
		return p_sequencer.get_by_name(name);
	endfunction : get_by_name

	task write_reg(cag_rgm_base reg_);
		bit bitstream[];
		int bits;
		cag_rgm_transfer trans;

		uvm_packer packer = new();
		packer.big_endian = 0;

		bits = reg_.pack(bitstream,packer);
		//reg_.print();

		`uvm_create(trans)
		trans.command = CAG_RGM_WRITE;
		trans.address = reg_.get_address();
		trans.data = 64'd0;
		//for(int i = 0 , int j = bits-1; i < bits; i++ ,j--)
		//  trans.data[i] = bitstream[j];

		for(int i = 0; i < bits; i++)
			trans.data[i] = bitstream[i];
		//$display("%b",trans.data);
		
		//uvm_report_info("DEBUG",$psprintf("write; address: %h, data: %h",trans.address,trans.data),UVM_NONE);

		`uvm_send(trans)
		//uvm_report_info("DEBUG",$psprintf("write; address: %h, data: %h done",trans.address,trans.data),UVM_NONE);
	endtask : write_reg

	task read_reg(cag_rgm_base reg_);
		int unsigned source_tag;
		bit bitstream[];
		int bits;
		cag_rgm_transfer trans;
		cag_rgm_transfer response;

		uvm_packer packer = new();
		packer.big_endian = 0;

		p_sequencer.m_get_source_tag(source_tag);
        //uvm_report_info("DEBUG",$psprintf("using tag: %0d",source_tag),UVM_NONE);

		bits = reg_.pack(bitstream,packer);

		`uvm_create(trans)
		trans.command = CAG_RGM_READ;
		trans.address = reg_.get_address();
		trans.source_tag = source_tag;
		//uvm_report_info("DEBUG",$psprintf("read; address: %h, data: %h",trans.address,trans.data),UVM_NONE);                      
		`uvm_send(trans)

		//-- wait for response
		//p_sequencer.responses.get(response);
		//if(response.source_tag != source_tag)
		//	p_sequencer.uvm_report_fatal(get_type_name(),$psprintf("got the wrong source tag: %h",response.source_tag));
		p_sequencer.get_response(source_tag, response);
        
		for(int i = 0 /*, int j = bits-1*/; i < bits; i++ /*, j--*/)
			bitstream[i] = response.data[i];

		bits = reg_.unpack(bitstream,packer);

		p_sequencer.m_release_source_tag(source_tag);
		//uvm_report_info("DEBUG",$psprintf("read; address: %h, data: %h done",response.address,response.data),UVM_NONE);
	endtask : read_reg

endclass : cag_rgm_sequence

class cag_rgm_write_sequence extends cag_rgm_sequence;

	rand cag_rgm_base req_;

	//`uvm_sequence_utils(cag_rgm_write_sequence, cag_rgm_sequencer)
	`uvm_object_utils(cag_rgm_write_sequence)

	function new(string name="cag_rgm_write_sequence");
		super.new(name);
	endfunction : new

	task body();
		cag_rgm_base m_req_;
		
		//p_sequencer.uvm_report_info(get_type_name(), $psprintf("Write Request:\n%s ",req_.sprint()),UVM_NONE);
		$cast(m_req_,req_.clone());
		
		write_reg(m_req_);
		
		req_.copy(m_req_);
	endtask : body

endclass : cag_rgm_write_sequence

class cag_rgm_read_sequence extends cag_rgm_sequence;

	rand cag_rgm_base req_;

	`uvm_object_utils(cag_rgm_read_sequence)

	function new(string name="cag_rgm_read_sequence");
		super.new(name);
	endfunction : new

	task body();
		cag_rgm_base m_req_;
		cag_rgm_base old_reg;
		
		//req_ = cag_rgm_base::type_id::create("m_req");
		//req_.copy(req_);
		$cast(m_req_,req_.clone());

		if (m_req_.get_check_on_read() == 1) begin//-- checking is enabled, so make a copy to compare afterwards
			$cast(old_reg,m_req_.clone());
		end

		//if (m_req_.get_check_on_read() == 1) 
		//	p_sequencer.uvm_report_info(get_type_name(), $psprintf("Read Request:\n%s\n, Saved:\n%s ",m_req_.sprint(),old_reg.sprint()),UVM_NONE);
		read_reg(m_req_);

		//uvm_report_info(get_type_name(),$psprintf("Compare of:\n%s\n%s",m_req_.sprint(),old_reg.sprint()),UVM_NONE);

		if (m_req_.get_check_on_read() == 1) begin 

			if (m_req_.compare(old_reg) != 1)
				p_sequencer.uvm_report_fatal(get_type_name(),
				$psprintf("Compare for check_on_read failed for:\n%s\nShould be:\n%s\nMaybe checking on this register has to be turned off. ",m_req_.sprint(), old_reg.sprint()));
		end
		
		req_.copy(m_req_);
	endtask : body

endclass : cag_rgm_read_sequence

/******************************************************************************
	*
	* REVISION HISTORY:
	*    
*******************************************************************************/
