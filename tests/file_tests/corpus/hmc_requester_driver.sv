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
`ifndef HMC_REQUESTER_DRIVER_SV
`define HMC_REQUESTER_DRIVER_SV

/* Driver is incomplete and not tested */
/* Use at your own risk */


class hmc_requester_driver #(parameter NUM_LANES=16) extends hmc_driver_base#(NUM_LANES);

	`uvm_component_param_utils(hmc_requester_driver#(.NUM_LANES(NUM_LANES)))

	function new(string name="hmc_requester_driver", uvm_component parent);
		super.new(name,parent);
		hmc_frp_port	= new("hmc_frp_port", this); 
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		local_config = link_config.requester;
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		super.run_phase(phase);

		forever begin
			if(vif.P_RST_N !== 1) begin
				next_state = RESET;
			end

			if (next_state != last_state)
				`uvm_info(get_type_name(),$psprintf("in state %s", next_state.name()), UVM_HIGH)

			last_state = next_state;

			fork
				begin
					case (next_state)
						RESET: reset();
						NULL_FLITS: null_flits();
						TS1: ts1();
						NULL_FLITS_2: null_flits_2();
						INITIAL_TRETS: initial_trets();
						LINK_UP: link_up();
						START_RETRY_INIT: start_retry_init();
						CLEAR_RETRY: clear_retry();
						SEND_RETRY_PACKETS: send_retry_packets();

					endcase
				end
				begin
					@(negedge vif.P_RST_N);

				end
				begin
				//	get_packets();
				end
			join_any
			disable fork;
		end

	endtask : run_phase

	task reset();

		vif.RXP = {NUM_LANES {1'bz}};
		vif.RXN = {NUM_LANES {1'bz}};
		vif.RXPS = 1'b1;
		

		seq_num = 1;
		last_rrp = 0;
		init_continue = 0;
		can_continue = 1;
		retry_buffer.reset();

		//wait for reset signal
		@(posedge vif.P_RST_N);

		#link_config.tINIT;

		set_init_continue();
		`uvm_info(get_type_name(),$psprintf("active = %0d retry prob = %0d", local_config.active, local_config.random_retry_probability), UVM_HIGH)

		vif.RXPS = 1'b1;

		#1us;
		reset_timestamp = $time;

		next_state = NULL_FLITS;
	endtask : reset

	task null_flits();
		int null_time;

		reset_lfsr();

		//wait for Responder to send NULLs
		while (!remote_status.get_all_lanes_locked())
			drive_fit({NUM_LANES {1'b0}});

		null_timestamp = $time;

		//wait at most tRESP2
		null_time_randomization_succeeds : assert (std::randomize(null_time) with {null_time > 0ns && null_time < link_config.tRESP2;});
		for (int i=0; i<null_time/link_config.bit_time; i++) begin
			drive_fit({NUM_LANES {1'b0}});
		end

		next_state = TS1;
	endtask : null_flits

	task ts1();
		int ts1_fits = 0;

		// Save the timestamp
		ts1_timestamp = $time;

		//wait for Responder to send TS1
		while (!remote_status.get_all_lanes_aligned())
			send_ts1(256); // 16 fits per sequence number, 16 sequence numbers

		//Send some (possibly incomplete) TS1 flits
		ts1_fits_randomization_succeeds : assert (std::randomize(ts1_fits) with {ts1_fits >= 0 && ts1_fits < 512;});
		send_ts1(ts1_fits);

		next_state = NULL_FLITS_2;
	endtask : ts1

	task null_flits_2();
		int null_flit_count;

		while (!remote_status.get_first_tret_received())
			drive_flit(128'h0);

		null_flit_count_randomization_succeeds : assert (std::randomize(null_flit_count) with {null_flit_count >= 1 && null_flit_count < 512;});

		//send NULL FLITs
		for (int i=0; i < null_flit_count; i++)
			drive_flit(128'h0);

		next_state = INITIAL_TRETS;
	endtask : null_flits_2

	function void drive_lanes(input bit[NUM_LANES-1:0] new_value);
		int i;

		bit[NUM_LANES-1:0] lanes_reordered;

		if (local_config.reverse_lanes) begin
			for (i = 0; i < NUM_LANES; i= i+1) begin
				lanes_reordered[i] = new_value[NUM_LANES-i-1];
			end
		end else begin
			lanes_reordered = new_value;
		end

		// TODO: wire delays?
		for (i = 0; i < local_config.width; i= i+1) begin
			vif.RXP[i] = lanes_reordered[i] ^ local_config.reverse_polarity[i]; 
			vif.RXN[i] = ~lanes_reordered[i] ^ local_config.reverse_polarity[i]; 
		end
	endfunction : drive_lanes

endclass : hmc_requester_driver

`endif // HMC_REQUESTER_DRIVER_SV

