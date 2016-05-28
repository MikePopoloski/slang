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

`ifndef AXI4_STREAM_MASTER_DRIVER_SV
`define AXI4_STREAM_MASTER_DRIVER_SV

class axi4_stream_master_driver #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends uvm_driver #(axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)));

	axi4_stream_config axi4_stream_cfg;

	virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) vif;

	`uvm_component_param_utils_begin(axi4_stream_master_driver #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))
		`uvm_field_object(axi4_stream_cfg, UVM_DEFAULT)
	`uvm_component_utils_end

	function new(string name="axi4_stream_master_driver", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		if(!uvm_config_db#(virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))::get(this, "", "vif",vif) ) begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		super.run_phase(phase);

		forever begin
			if(vif.ARESET_N !== 1) begin
				vif.TVALID <= 0;
				`uvm_info(get_type_name(),$psprintf("reset"), UVM_HIGH)
				@(posedge vif.ARESET_N);
				`uvm_info(get_type_name(),$psprintf("coming out of reset"), UVM_HIGH)
			end

			fork
				begin //-- Asynchronous reset
					@(negedge vif.ARESET_N);
				end
				begin
					drive_valid_cycles();
				end
			join_any
			disable fork;
		end

	endtask : run_phase
	
	task drive_valid_cycles();
		@(posedge vif.ACLK);
		
		forever begin
			axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) vc;
			
			//-- Try next AXI4 item
			seq_item_port.try_next_item(vc);
			if( vc != null) begin
				`uvm_info(get_type_name(),$psprintf("There is an item to sent"), UVM_MEDIUM)
				`uvm_info(get_type_name(),$psprintf("send %0x %0x", vc.tuser, vc.tdata), UVM_MEDIUM)
				
				//-- Wait until delay
				repeat(vc.delay)
					@(posedge vif.ACLK);
				
				//-- Send AXI4 cycle
				vif.TDATA  <= vc.tdata;
				vif.TUSER  <= vc.tuser;
				vif.TVALID <= 1;
				@(posedge vif.ACLK)
				while(vif.TREADY == 0)
					@(posedge vif.ACLK);
				
				vif.TUSER  <= 0;
				vif.TDATA  <= 0;
				vif.TVALID <= 0;
				`uvm_info(get_type_name(),$psprintf("send done: %0x %0x", vc.tuser, vc.tdata), UVM_MEDIUM)
				
				seq_item_port.item_done();
			end else //-- Else wait 1 cycle
				@(posedge vif.ACLK);

		end
	endtask : drive_valid_cycles

endclass : axi4_stream_master_driver

`endif  //AXI4_STREAM_MASTER_DRIVER_SV
