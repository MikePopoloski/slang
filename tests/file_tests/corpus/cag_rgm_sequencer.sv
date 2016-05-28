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

typedef class cag_rgm_write_sequence;
typedef class cag_rgm_read_sequence;

class cag_rgm_sequencer extends uvm_sequencer #(cag_rgm_transfer);

	 `uvm_analysis_imp_decl(_resp)
    uvm_analysis_imp_resp #(cag_rgm_transfer,cag_rgm_sequencer) resp_port;
    
    int unsigned source_tag_count = 1;
    protected mailbox #(int unsigned) source_tags;
    
    protected cag_rgm_register_file m_rf;
    protected cag_rgm_write_sequence write_seq;
    protected cag_rgm_read_sequence read_seq;
    
    protected mailbox #(cag_rgm_transfer) responses_mb;
    cag_rgm_transfer responses_q[$];
    semaphore responses_s;
    event     new_rsp;
	
    //`uvm_sequencer_utils_begin(cag_rgm_sequencer)
    //    `uvm_field_int(source_tag_count, UVM_ALL_ON)
    //`uvm_sequencer_utils_end
    `uvm_component_utils_begin(cag_rgm_sequencer)
        `uvm_field_int(source_tag_count, UVM_ALL_ON)
    `uvm_component_utils_end
	
	function new(string name = "cag_rgm_sequencer",uvm_component parent);
		super.new(name,parent);
		//count = 0;
		//`uvm_update_sequence_lib
		
		resp_port = new("resp_port",this);
		responses_mb = new();
		responses_s = new(1);
		source_tags = new();
	endfunction : new
	
	function void build();
		super.build();
		
		for(int unsigned i = 0; i < source_tag_count; i++)
			void'(source_tags.try_put(i));		
	endfunction : build
    
    task run();
        cag_rgm_transfer response;
        
        forever begin
            responses_mb.get(response);
            //uvm_report_info("DEBUG",$psprintf("received rsp with tag %0d",response.source_tag),UVM_NONE);
            //$stop;
            responses_s.get(1);
            responses_q.push_back(response);
            ->new_rsp;
            responses_s.put(1);
            //$stop;
        end
    endtask : run
	
	function void set_rf(cag_rgm_register_file rf);
		this.m_rf = rf;
	endfunction : set_rf
	
	function void write_resp(input cag_rgm_transfer transfer);
		if(transfer.command == CAG_RGM_READ_RESPONSE)
			assert(responses_mb.try_put(transfer));
	endfunction : write_resp
    
    task get_response(int unsigned source_tag, ref cag_rgm_transfer rsp);
        
        //responses.get(rsp);
        //if(rsp.source_tag != source_tag)
        //    p_sequencer.uvm_report_fatal(get_type_name(),$psprintf("got the wrong source tag: %h",rsp.source_tag));
        forever begin
            responses_s.get(1);
            while(responses_q.size() == 0) begin
                responses_s.put(1);
                //$stop;
                @new_rsp;
                //$stop;
                responses_s.get(1);
            end
            
            foreach(responses_q[i]) begin
               //uvm_report_info("DEBUG",$psprintf("foreach tag: %0d",responses_q[i].source_tag),UVM_NONE);
               if(responses_q[i].source_tag == source_tag) begin
                  rsp = responses_q[i];
                  responses_q.delete(i);
                  responses_s.put(1);
                  //$stop;                  
                  return;
               end 
            end
            
            responses_s.put(1);
            //$stop;
            @new_rsp;
        end
        
    endtask : get_response
	
	task m_get_source_tag(output int unsigned tag);
		source_tags.get(tag);
	endtask : m_get_source_tag
	
	task m_release_source_tag(int unsigned tag);
		source_tags.put(tag);
	endtask : m_release_source_tag
		
	//
	// rf access functions
	//
	function cag_rgm_base get_by_name(string name = "");
		return m_rf.get_by_name(name);
	endfunction : get_by_name
	
	function cag_rgm_base get_by_address(bit [63:0] address);
		return m_rf.get_by_address(address);
	endfunction : get_by_address
	
	task write_reg(cag_rgm_base reg_);
		write_seq = cag_rgm_write_sequence::type_id::create("write_seq");
		write_seq.req_ = reg_;
		write_seq.start(this);
	endtask : write_reg
	
	task read_reg(cag_rgm_base reg_);
		read_seq = cag_rgm_read_sequence::type_id::create("read_seq");
		read_seq.req_ = reg_;
		read_seq.start(this);
	endtask : read_reg
	
endclass : cag_rgm_sequencer

/******************************************************************************
*
* REVISION HISTORY:
*    
*******************************************************************************/

