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
`ifndef HMC_RESPONDER_DRIVER_SV
`define HMC_RESPONDER_DRIVER_SV

class hmc_responder_driver#(parameter NUM_LANES=16) extends hmc_driver_base#(NUM_LANES);
	bit clear_error = 0;

	`uvm_component_param_utils(hmc_responder_driver#(.NUM_LANES(NUM_LANES)))

	function new(string name="hmc_responder_driver", uvm_component parent);
		super.new(name,parent);
		hmc_frp_port	= new("hmc_frp_port", this); 
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		start_clear_retry_event = new("start_retry_event");
		local_config = link_config.responder;

		if (!local_config.requester) begin
		tokens_to_send = link_config.hmc_tokens;

		`uvm_info(get_type_name(),$psprintf("initial_trets token_count = %0d", link_config.hmc_tokens), UVM_NONE)
		end else begin
			tokens_to_send = link_config.rx_tokens;

			`uvm_info(get_type_name(),$psprintf("initial_trets token_count = %0d", link_config.rx_tokens), UVM_NONE)
		end
		token_count_not_zero : assert (tokens_to_send > 0);
	endfunction : build_phase

	task run_phase(uvm_phase phase);
		super.run_phase(phase);

		forever begin
			if(vif.P_RST_N !== 1) begin
				next_state = RESET;
			end

			fork
				forever begin
					if (next_state != state) begin
						`uvm_info(get_type_name(),$psprintf("in state %s", next_state.name()), UVM_HIGH)
					end
					

					last_state = state;
					state = next_state;

					case (state)
						RESET: reset();
						POWER_DOWN: power_down();
						INIT: init();
						PRBS: prbs();
						NULL_FLITS: null_flits();
						TS1: ts1();
						NULL_FLITS_2: null_flits_2();
						INITIAL_TRETS: initial_trets();
						LINK_UP: link_up();
						START_RETRY_INIT: start_retry_init();
						CLEAR_RETRY: clear_retry();
						SEND_RETRY_PACKETS: send_retry_packets();
					endcase
					clear_error = 0;
				end
				begin
					@(negedge vif.P_RST_N);
				end
				forever begin
					start_clear_retry_event.wait_ptrigger();
					start_clear_retry_event.reset(0);
					next_state = CLEAR_RETRY;
					`uvm_info(get_type_name(), "start retry event was triggered", UVM_HIGH)
					clear_error = 1;
				end
				begin
					time wait_time;
					@(negedge vif.RXPS);
					power_down_time_success : assert (std::randomize(wait_time) with { wait_time>0 && wait_time <= link_config.t_PST + 3*link_config.t_SS;});
					#wait_time;
					vif.TXPS = 0;
					link_down_time_success : assert (std::randomize(wait_time) with { wait_time>0 && wait_time <= link_config.t_SME;});
					#wait_time;
					next_state = POWER_DOWN;
				end
				clk_gen();
			join_any;
			disable fork;
		end

	endtask : run_phase

	task reset();

		vif.TXP = {NUM_LANES {1'bz}};
		vif.TXN = {NUM_LANES {1'bz}};
		vif.TXPS = 1'bz;
		vif.FERR_N = 1'bz;

		seq_num = 1;
		last_rrp = 0;
		init_continue = 0;
		can_continue = 0;
		retry_buffer.reset();

		//wait for reset signal
		@(posedge vif.P_RST_N);
		reset_timestamp = $time;

		next_state = INIT;
	endtask : reset

	task power_down();
		time wait_time;

		clear_lanes();
		vif.TXP = {NUM_LANES {1'bz}};
		vif.TXN = {NUM_LANES {1'bz}};
		
		recover_from_power_down = 1;
		
		@(posedge vif.RXPS)
		//-- wait some time < t_pst
		power_up_time_success : assert (std::randomize(wait_time) with { wait_time>0 && wait_time <= link_config.t_PST + 3*link_config.t_SS;});
		#wait_time;
		vif.TXPS = 1;
		//-- wait some time < t_sme
		link_up_time_success : assert (std::randomize(wait_time) with { wait_time>0 && wait_time <= link_config.t_SME;});
		#wait_time;
		next_state = PRBS;
		
	endtask : power_down
	
	task init();

		//wait for tINIT to pass
		while ($time < reset_timestamp + link_config.tINIT)
			@(posedge vif.REFCLKP);

		can_continue = 1;

		// TODO: Think of the "right" place to do this.
		// The problem is that it should happen in the sideband.
		// In our case, the sideband is software-controlled, not part of the controller.
		set_init_continue();
		`uvm_info(get_type_name(),$psprintf("active = %0d retry prob = %0d", local_config.active, local_config.random_retry_probability), UVM_HIGH)

		//wait for init_continue to be set
		while (!init_continue)
			@(posedge vif.REFCLKP);

		//Set TXPS high
		vif.TXPS = 1'b1;

		//@(posedge vif.REFCLKP);

		next_state = PRBS;
	endtask : init

	task prbs();
		int prbs_time;

		prbs_timestamp = $time;

		// send PRBS at least until Requester locks
		while (!(remote_status.current_state > PRBS))
			for (int i=0; i < 4; i++)
				drive_fit({NUM_LANES/2 {i[1:0]}});

		// Randomize PRBS length
		prbs_time_randomization_succeeds : assert (std::randomize(prbs_time) with {prbs_time > 0ns && prbs_time < link_config.tRESP1;});
		`uvm_info(get_type_name(),$psprintf("prbs_time = %0d (between %0d and %0d)", prbs_time, 0ns, link_config.tRESP1), UVM_HIGH)

		for (int i=0; i < prbs_time/link_config.bit_time; i++) begin
			drive_fit({NUM_LANES/2 {i[1:0]}});
		end

		next_state = NULL_FLITS;
	endtask : prbs

	task null_flits();
		int null_time;

		null_timestamp = $time;

		reset_lfsr();

		//wait for Requester to send TS1
		while (!(remote_status.current_state >NULL_FLITS))
			drive_fit({NUM_LANES {1'b0}});

		req_ts1_timestamp = $time;

		//wait at most tRESP2
		null_time_randomization_succeeds : assert (std::randomize(null_time) with {null_time > 0ns && null_time < link_config.tRESP2;});
		`uvm_info(get_type_name(),$psprintf("null time = %0d ", null_time), UVM_HIGH)
		for (int i=0; i<null_time/link_config.bit_time-1; i++) begin
			drive_fit({NUM_LANES {1'b0}});
		end

		next_state = TS1;
	endtask : null_flits

	task ts1();
		int ts1_fits = 0;

		// Save the timestamp
		ts1_timestamp = $time;
		`uvm_info(get_type_name(), $psprintf("Sending TS1 Sequences"),UVM_MEDIUM)
		//wait for Requester to send NULL FLITs
		while (!(remote_status.current_state>TS1))
			send_ts1(256); // 16 fits per sequence number, 16 sequence numbers

		next_state = NULL_FLITS_2;
	endtask : ts1

	task null_flits_2();
		int null_flit_count;

		null_flit_count_randomization_succeeds : assert (std::randomize(null_flit_count) with {null_flit_count >= 32 && null_flit_count < 512;});

		//send NULL FLITs
		for (int i=0; i < null_flit_count; i++)
			drive_flit(128'h0);

		next_state = INITIAL_TRETS;
	endtask : null_flits_2

	function void drive_lanes(input bit[NUM_LANES-1:0] new_value);
		int i;

		bit[NUM_LANES-1:0] lanes_reordered;

		if (local_config.reverse_lanes) begin
			for (i = 0; i < local_config.width; i= i+1) begin
				lanes_reordered[i] = new_value[local_config.width-i-1];
			end
		end else begin
			lanes_reordered = new_value;
		end

		for (i = 0; i < local_config.width; i= i+1) begin
			bit set;
			lane_queues[i].push_back(lanes_reordered[i]  ^ local_config.reverse_polarity[i]);
			
			if (local_config.lane_delays[i] <= lane_queues[i].size()) begin
				set = lane_queues[i].pop_front();
				vif.TXP[i] = set;
				vif.TXN[i] = ~set; 
			end
		end
	endfunction : drive_lanes

	task clear_lanes();
		//-- while lane_queues.size >0
		int i;
		bit empty = 1;
		while(empty) begin
			empty =0;
			@driver_clk;
			for (i = 0; i < local_config.width; i= i+1) begin
					logic set;
				if (lane_queues[i].size>0) begin
					empty = 1;
					set = lane_queues[i].pop_front();
					vif.TXP[i] = set;
					vif.TXN[i] = ~set; 
				end	else begin
					vif.TXP[i] = 1'bz;
					vif.TXN[i] = 1'bz;
				end
			end
		end
	endtask : clear_lanes

endclass : hmc_responder_driver

`endif // HMC_RESPONDER_DRIVER_SV

