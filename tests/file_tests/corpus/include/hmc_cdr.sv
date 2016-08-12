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
`ifndef hmc_cdr_SV
`define hmc_cdr_SV
class hmc_cdr #(parameter NUM_LANES = 16) extends uvm_component;
	
	event int_clk;

	virtual hmc_sr_if#(.NUM_LANES(NUM_LANES)) vif;
	hmc_link_config link_config;
	
	link_type_t link_type = REQUESTER;

	`uvm_component_param_utils_begin(hmc_cdr#(.NUM_LANES(NUM_LANES)))
		`uvm_field_enum(link_type_t, link_type, UVM_DEFAULT)
	`uvm_component_utils_end
	
	function new ( string name="hmc_cdr", uvm_component parent );
		super.new(name, parent);
	endfunction : new
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if(uvm_config_db#(hmc_link_config )::get(this, "", "link_config",link_config) ) begin
			this.link_config = link_config;
		end else begin
			`uvm_fatal(get_type_name(),"link_config is not set")
		end
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "vif",vif) ) begin
			this.vif = vif;
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end
	endfunction : build_phase
	
	
	task run_phase(uvm_phase phase);
		bit timeout = 0;
		
		time timeout_length;
		time wait_time;
		
		super.run_phase(phase);
		
		forever begin
			
			@(posedge vif.P_RST_N); //-- wait for leaving reset state
			fork 
				begin 
					@(negedge vif.P_RST_N);	//-- entering reset state
				end
				begin
					
					timeout_length = link_config.bit_time;
					
					forever begin
						fork
							begin 
								if(link_type == REQUESTER)
									@(vif.RXP);
								else
									@(vif.TXP);
							end
							begin 
								#(timeout_length + 1ps);
								timeout = 1;
							end
						join_any
						disable fork;
						
						case (link_config.bit_time)
							100ps	: wait_time = 50ps;
							80ps	: wait_time = 40ps;
							66ps	: wait_time = 30ps;
						endcase
						
						timeout_length = wait_time;
						
						if(timeout == 1)
							wait_time -= 1ps;
						
						#(wait_time);
						
						-> int_clk;
						
						timeout = 0;
					end
				end
			join_any;
			disable fork;
		end
	endtask : run_phase
	
endclass :hmc_cdr

`endif //hmc_cdr_SV