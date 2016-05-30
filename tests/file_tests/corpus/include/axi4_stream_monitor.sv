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
// axi4_stream_packet monitor
//
//

`ifndef AXI4_STREAM_MONITOR_SV
`define AXI4_STREAM_MONITOR_SV

class axi4_stream_monitor #(parameter DATA_BYTES = 16, parameter TUSER_WIDTH = 16) extends uvm_monitor;

	virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) 				vif;

	uvm_analysis_port #(axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH))) 	item_collected_port;

	
	`uvm_component_param_utils(axi4_stream_monitor #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))
	
	
	function new ( string name="axi4_stream_monitor", uvm_component parent );
		super.new(name, parent);

		item_collected_port = new("item_collected_port", this);

	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		if(uvm_config_db#(virtual interface axi4_stream_if #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)))::get(this, "", "vif",vif) ) begin
			this.vif = vif;
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end

	endfunction : build_phase

	
	task run();
		axi4_stream_valid_cycle #(.DATA_BYTES(DATA_BYTES), .TUSER_WIDTH(TUSER_WIDTH)) vc;
		
		forever begin
			if (vif.ARESET_N !== 1)
			begin
				@(posedge vif.ARESET_N);
			end

			fork
				begin //-- Asynchronous reset
					@(negedge vif.ARESET_N);
				end


				forever begin
					//-- At the positive edge of ACLK
					@(posedge vif.ACLK);

					//-- Capture valid bus cycles
					vc = new();

					if (vif.TVALID == 1 && vif.TREADY == 1) begin

						vc.tuser 	= vif.TUSER;
						vc.tdata 	= vif.TDATA;
						item_collected_port.write(vc);
						`uvm_info(get_type_name(),$psprintf("valid cycle tuser %0x tdata %0x", vc.tuser, vc.tdata), UVM_HIGH)

					end

					//-- used to detect the hmc_pkt_delay between packets
					if (vif.TVALID == 0) begin
						vc.tuser	= {TUSER_WIDTH{1'b0}};
						vc.tdata	= {DATA_BYTES{8'b0}};;
						item_collected_port.write(vc);
					end

				end
			join_any
			disable fork;


		end
	endtask : run

endclass : axi4_stream_monitor

`endif // AXI4_STREAM_MONITOR_SV
