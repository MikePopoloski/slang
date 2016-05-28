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
// hmc_packet monitor
//
//

`ifndef HMC_MONITOR_SV
`define HMC_MONITOR_SV

class hmc_monitor#(parameter NUM_LANES = 16) extends uvm_monitor;
	
	virtual hmc_sr_if#(.NUM_LANES(NUM_LANES)) vif;
	
	hmc_link_config link_config;
	hmc_local_link_config local_config;
	hmc_status status;
	hmc_link_status link_status;
	hmc_link_status remote_link_status;
	hmc_transaction_mon transaction_mon;
	hmc_cdr #(.NUM_LANES(NUM_LANES)) cdr;

	uvm_analysis_port #(hmc_packet) item_collected_port;
	uvm_analysis_port #(hmc_packet) return_token_port;
	uvm_analysis_port #(hmc_packet) frp_port;
	uvm_analysis_port #(int)	rrp_port;

	uvm_event start_clear_retry_event;
	event lane_queue_event;			//-- triggers after write to any lane queue
	event flit_queue_event;		//-- triggers after write to the collected_flits queue
	
	// Partial flits from each lane
	typedef bit [14:0] lsfr_t;
	typedef bit [15:0]	partial_flit_t;
	typedef bit [127:0] flit_t;
	// Queue of unassembled flits (per lane)
	typedef partial_flit_t			partial_flit_queue_t[$];
	partial_flit_queue_t			lane_queues[];
	
	
	
	bit [2:0]	next_sequence_num;
	bit lane_reversal_set = 0;//-- TODO move to link_status
	
	bit bitstream[$];
	bit [127:0]	collected_flits[$];	
	

	hmc_packet		collected_packet;

	//-- reporting counter
	int lng_error = 0;
	int crc_error = 0;
	int seq_error = 0;
	int poisoned_pkt =0;


	typedef enum {
		LENGTH_ERROR,
		CRC_ERROR,
		SEQ_ERROR,	
		POISON,
		INVALID_TS1
	}error_class_e;
	
	//-- coverage --//
	int packets_after_Link_up 	= 0;
	int start_retry_count 		= 0;
	int clear_error_abort_count	= 0;
	error_class_e current_error;
	
	int null_flits_after_TS1	= 0;
	int null_flits_between_pkts	= 0;
	
	
	covergroup hmc_pkt_error_cg;
		option.per_instance = 1;
		ERROR_TYPE: coverpoint current_error;

		HMC_COMMAND: coverpoint collected_packet.command {
			bins flow_types[] = {
				HMC_TRET,
				HMC_PRET,
				HMC_NULL,
				HMC_IRTRY
			};
			bins requests[] = {
				HMC_WRITE_16,
				HMC_WRITE_32,
				HMC_WRITE_48,
				HMC_WRITE_64,
				HMC_WRITE_80,
				HMC_WRITE_96,
				HMC_WRITE_112,
				HMC_WRITE_128,
				
				HMC_MODE_WRITE,
				HMC_BIT_WRITE,
				HMC_DUAL_8B_ADDI,
				HMC_SINGLE_16B_ADDI,
				
				HMC_POSTED_WRITE_16,
				HMC_POSTED_WRITE_32,
				HMC_POSTED_WRITE_48,
				HMC_POSTED_WRITE_64,
				HMC_POSTED_WRITE_80,
				HMC_POSTED_WRITE_96,
				HMC_POSTED_WRITE_112,
				HMC_POSTED_WRITE_128,
				HMC_POSTED_BIT_WRIT,
				
				HMC_POSTED_BIT_WRIT,
				HMC_POSTED_DUAL_8B_ADDI,
				HMC_POSTED_SINGLE_16B_ADDI,
				
				HMC_MODE_READ,
				HMC_READ_16,
				HMC_READ_32,
				HMC_READ_48,
				HMC_READ_64,
				HMC_READ_80,
				HMC_READ_96,
				HMC_READ_112, 
				HMC_READ_128};

			bins response[] = {
				HMC_READ_RESPONSE,
				HMC_WRITE_RESPONSE,
				HMC_MODE_READ_RESPONSE,
				HMC_MODE_WRITE_RESPONSE,
				HMC_ERROR_RESPONSE
			};
			illegal_bins n_used = default;
		}
		CROSS_ERROR_TYPPE_COMMAND : cross ERROR_TYPE, HMC_COMMAND {
			ignore_bins SEQ_IGNORE    = binsof(ERROR_TYPE) intersect {SEQ_ERROR} && binsof(HMC_COMMAND) intersect {HMC_NULL, HMC_PRET, HMC_IRTRY};
			ignore_bins POISON_IGNORE = binsof(ERROR_TYPE) intersect {POISON} && binsof(HMC_COMMAND) intersect {HMC_NULL};
		}
	endgroup


	covergroup null2_cg;
		option.per_instance = 1;
		NULL2_count : coverpoint null_flits_after_TS1+ null_flits_between_pkts{	//-- Link_up is reached after 32 consecutive flits
			illegal_bins ib = {[0:31]};
			bins minimum_amount	= {32};
			bins low_amount[]	= {[33:50]};
			bins medium_amount[] = {[51:100]};
			bins high_amount 	= {[101:$]};
		}
	endgroup


	covergroup hmc_packets_cg;
		option.per_instance = 1;

		NULLS_BETWEEN_PACKETS : coverpoint null_flits_between_pkts{
			bins low_amount[]	= {[0:20]};
			bins medium_amount[]	= {[21:199]};
			bins high_amount	={[200:$]};
		}
		COMMAND : coverpoint collected_packet.command;
		PAYLOAD_LENGTH : coverpoint collected_packet.duplicate_length -1{
			bins no_payload = {0};
			bins payload[] = {[1:8]};
		}
		CROSS_COMMAND_NULLS : cross COMMAND,NULLS_BETWEEN_PACKETS;
	endgroup


	covergroup hmc_link_cg;
		option.per_instance = 1;
		LINK_REVERSAL	: coverpoint link_status.lane_reversed;
		Link_WIDTH		: coverpoint NUM_LANES{
			bins half_width = {8};
			bins full_width = {16};
		}
		CROSS_LANE_LINK_REVERSAL_WIDTH : cross Link_WIDTH, LINK_REVERSAL;
	endgroup


	covergroup tokens_cg;
		option.per_instance = 1;
		TOKEN_AVAILABLE : coverpoint link_status.token_count{
			bins no_token_available = {0};
			bins very_low_amount_available[] = {[1:9]};
			bins low_amount_available[] = {[10:30]};
			bins medium_amount_available[] = {[31:100]};
			bins high_amount_available = {[101:$]};
		}
		FPW : coverpoint link_config.fpw {
			bins legal_fpw[] = {2,4,6,8};
		}
		CROSS_FPW_TOKENS : cross FPW, TOKEN_AVAILABLE;
	endgroup

	`uvm_component_param_utils(hmc_monitor#(.NUM_LANES(NUM_LANES)))


	function new ( string name="hmc_monitor", uvm_component parent );

		super.new(name, parent);
		
		lane_queues = new[NUM_LANES] (lane_queues);
		
		hmc_pkt_error_cg	= new();
		hmc_packets_cg		= new();
		hmc_link_cg			= new();
		tokens_cg 			= new();
		null2_cg			= new();
		
		item_collected_port = new("item_collected_port", this);
		return_token_port 	= new("return_token_port", this);
		frp_port 			= new("frp_port", this);
		rrp_port 			= new("rrp_port", this);
		next_sequence_num 	= 3'b1;
		
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "vif",vif) ) begin
			this.vif = vif;
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")
		end
		if(!uvm_config_db#(hmc_link_config)::get(this, "", "link_config",link_config) ) begin
			`uvm_fatal(get_type_name(),"link_config is not set")
		end
		
		if(!uvm_config_db#(hmc_local_link_config)::get(this, "", "local_config",local_config) ) begin
			`uvm_fatal(get_type_name(),"local_config is not set")
		end
		
	
		if(!uvm_config_db#(hmc_status)::get(this, "", "status",status) ) begin
			`uvm_fatal(get_type_name(),"Responder_link_status is not set")
		end
		
		if (item_collected_port == null)
			`uvm_fatal(get_type_name(), "uvm_analysis_port not ready")
		
		
		start_clear_retry_event = new ("start_retry_event");
		link_status = local_config.requester?status.Requester_link_status:status.Responder_link_status;
		remote_link_status = (!local_config.requester)?status.Requester_link_status:status.Responder_link_status;
		
		set_config_int("cdr", "link_type", local_config.requester?REQUESTER:RESPONDER);
		
		cdr = hmc_cdr#(.NUM_LANES(NUM_LANES))::type_id::create("cdr", this);

		// This should be a better check for the BFM.
		if (!link_config.responder.active) begin
			status.Responder_link_status.set_relaxed_token_handling(1);
		end
		
		
	endfunction : build_phase

	function logic get_bit(input bit Requester, input int lane);
		if (Requester)
			get_bit = vif.RXP[lane];
		else
			get_bit = vif.TXP[lane];
	endfunction : get_bit

	function bit check_lane_queues_not_empty();
		bit full = 1;
		foreach (lane_queues[i]) begin
			if (lane_queues[i].size()==0)
				full = 0;
		end
		return full;
	endfunction

	task check_clock();
		int i;
		int start_time = 0;
		int clock_period = 0;
		int expected_period = 0;

		`uvm_info(get_type_name(),$psprintf("started clock check %0d", $time), UVM_HIGH)
		forever begin

			if (vif.P_RST_N !== 1) // Reset
			begin
				@(posedge vif.P_RST_N);

				// Sample REFCLK_BOOT pins
				case (vif.REFCLK_BOOT)
					2'b00: expected_period = 8ns; // 125 MHz
					2'b01: expected_period = 6.4ns; // 156.25 MHz
					2'b10: expected_period = 6ns; // 166.66 MHz
					2'b11: `uvm_fatal(get_type_name(),$psprintf("REFCLK_BOOT setting %0d invalid!", vif.REFCLK_BOOT))
				endcase

				// Sample REFCLKP
				@(posedge vif.REFCLKP);
				start_time = $time;

				for (i=0;i<100;i++)
					@(posedge vif.REFCLKP);
				clock_period = ($time-start_time)/100;

				`uvm_info(get_type_name(),$psprintf("clock_period = %0d expected = %0d", clock_period, expected_period), UVM_HIGH)

				if (clock_period != expected_period)
					`uvm_fatal(get_type_name(),$psprintf("clock_period %0d (p) != expected %0d!", clock_period, expected_period));

				// Sample REFCLKN
				@(posedge vif.REFCLKN);
				start_time = $time;

				for (i=0;i<100;i++)
					@(posedge vif.REFCLKN);
				clock_period = ($time-start_time)/100;

				if (clock_period != expected_period)
					`uvm_fatal(get_type_name(),$psprintf("clock_period (n) %0d != expected %0d!", clock_period, expected_period));

			end
			@(negedge vif.P_RST_N);
		end
	endtask : check_clock

	task monitor_power_pins();
		if (local_config.requester) begin
			link_status.signal_power_state(vif.RXPS);
			forever begin
				@(vif.RXPS)
				if (vif.RXPS == 1'b0)
					CHK_IDLE_BEFORE_REQUESTER_POWERDOWN: assert (idle_check()) //-- check if Link is IDLE
				else begin
					`uvm_fatal(get_type_name(),$psprintf("link is not IDLE"))
				end
				link_status.signal_power_state(vif.RXPS);
			end
		end else begin
			link_status.signal_power_state(vif.TXPS);
			forever begin
				@(vif.TXPS)
				if (vif.TXPS == 1'b0)
					CHK_IDLE_BEFORE_RESPONDER_POWERDOWN: assert (idle_check())	//-- check if Link is IDLE
				else begin
					`uvm_fatal(get_type_name(),$psprintf("link is not IDLE"))
				end
				link_status.signal_power_state(vif.TXPS);
			end
		end
	endtask : monitor_power_pins

	task descramble(input int lane);
		partial_flit_t	partial_flit;
		lsfr_t	lfsr;
		lsfr_t	calculated_lfsr;
		bit		last_bit;
		bit		alligned = 0;
		int		run_length_count = 0;

		`uvm_info(get_type_name(),$psprintf("%s lane %0d descrambler started", local_config.requester?"Requester":"Responder", lane), UVM_HIGH)
		forever begin
			if (link_status.current_state == RESET || link_status.current_state == POWER_DOWN) /*RESET*/
			begin
				logic test;
				@(link_status.current_state);
				`uvm_info(get_type_name(), "Waiting for valid bit", UVM_HIGH)
				test = local_config.requester?vif.RXP[lane]:vif.TXP[lane];
				while (test === 1'bz)begin
					@(cdr.int_clk)
					test = local_config.requester?vif.RXP[lane]:vif.TXP[lane];
				end
			end

			else if (!link_status.get_locked(lane)) /*LOCK SCRAMBLER*/
			begin
				
				lfsr = calculated_lfsr;
				//-- Guess that the top bit is 0 to lock when scrambling is turned off
				calculated_lfsr[14] = (link_config.scramblers_enabled? 1'b1 : 1'b0);
				for (int i=0; i<14; i++)
				begin
					calculated_lfsr[i] = get_bit(local_config.requester,lane) ^ last_bit;
					last_bit = get_bit(local_config.requester,lane);

					@(cdr.int_clk);
					lfsr = {lfsr[1]^lfsr[0], lfsr[14:1]}; // step the LFSR
				end
				if (lane == 0)
					`uvm_info(get_type_name(),$psprintf("%s lane 0 calculated_lfsr=%0x lfsr=%0x", local_config.requester?"Requester":"Responder", calculated_lfsr, lfsr), UVM_HIGH)
				if (lfsr == calculated_lfsr) begin
					/*Inversion check*/
					if (get_bit(local_config.requester,lane) ^ lfsr[0]) begin
						link_status.set_inverted(lane);
						`uvm_info(get_type_name(),$psprintf("%s lane %0d is inverted", local_config.requester?"Requester":"Responder", lane),UVM_LOW)
					end
					Requester_locks_before_Responder : assert (local_config.requester || status.Requester_link_status.get_all_lanes_locked());
					link_status.set_locked(lane);
				end
			end 
			else if (!link_status.get_nonzero(lane)) /*WAIT FOR POSSIBLE TS1 (non-zero)*/
			begin
				`uvm_info(get_type_name(),$psprintf("locked on %s lane %0d inverted = %0x lfsr=%0x", local_config.requester?"Requester":"Responder", lane,link_status.get_inverted(lane), lfsr), UVM_HIGH)
				while (get_bit(local_config.requester,lane) ^ lfsr[0] ^ link_status.get_inverted(lane) == 0)
				begin
					lfsr = {lfsr[1]^lfsr[0], lfsr[14:1]}; //-- Every clock after lock, step the LFSR
					@(cdr.int_clk);
				end
				link_status.set_nonzero(lane);
			end 
			else if (!link_status.get_aligned(lane)) /*ALIGN WITH TS1*/
			begin

				`uvm_info(get_type_name(),$psprintf("looking for TS1 on %s lane %0d", local_config.requester?"Requester":"Responder", lane), UVM_HIGH)
				partial_flit[7:0] = 8'hff;
				while (!link_status.get_aligned(lane))	begin
					//-- shift until a possible TS1 sequence is detected
					
					partial_flit = partial_flit >> 1;
					partial_flit[7] = get_bit(local_config.requester,lane) ^ lfsr[0] ^ link_status.get_inverted(lane);
					lfsr = {lfsr[1]^lfsr[0], lfsr[14:1]}; //-- Every clock after lock, step the LFSR
					@(cdr.int_clk);
					
					if (partial_flit[7:0] == 8'hf0) begin //-- found potential TS1 sequence
						//-- check next partial flits
						alligned = 1;
						for (int i = 0; i <local_config.TS1_Messages; i++) begin
							//-- read next partial flit
							for (int i=0; i<16; i++) begin
								partial_flit[i] = get_bit(local_config.requester,lane) ^ lfsr[0] ^ link_status.get_inverted(lane);
								lfsr = {lfsr[1]^lfsr[0], lfsr[14:1]}; // Every clock after lock, step the LFSR
								@(cdr.int_clk);
							end
							`uvm_info(get_type_name(),$psprintf("partial_flit=%0x", partial_flit), UVM_HIGH)
							if (partial_flit[15:8] != 8'hf0)begin
								`uvm_info(get_type_name(),$psprintf("Alignment Error, retry"), UVM_NONE)
								alligned = 0;
								continue;//-- retry
							end
							if (alligned) begin
							link_status.set_aligned(lane);
							
							`uvm_info(get_type_name(),$psprintf("%s lane %0x aligned", local_config.requester?"Requester":"Responder", lane), UVM_HIGH)
							end
						end
					end
				end
				run_length_count = 0;
			end 
			else /*NORMAL OPERATION*/
			begin
				for (int i=0; i<16; i++)
				begin
					// Check Run current_packet_length limit
					if (last_bit == get_bit(local_config.requester,lane))
					begin
						run_length_count = run_length_count + 1;

						if ((run_length_count >= local_config.run_length_limit) && link_config.scramblers_enabled)
							`uvm_fatal(get_type_name(),$psprintf("last_bit=%0x repeated %0d times on %s lane %0d"
									, last_bit, run_length_count, local_config.requester?"Requester":"Responder", lane));
					end else begin
						run_length_count = 0;
						last_bit = !last_bit;
					end
					partial_flit[i] = get_bit(local_config.requester,lane) ^ lfsr[0] ^ link_status.get_inverted(lane);
					lfsr = {lfsr[1]^lfsr[0], lfsr[14:1]}; // Every clock after lock, step the LFSR
					
					@(cdr.int_clk);
				end
				lane_queues[lane].push_back(partial_flit);
				//-- lane_queue_event only after all partial flits present
				if(check_lane_queues_not_empty())
					-> lane_queue_event;
			end
		end
	endtask : descramble

	function void reset_link();
		lane_reversal_set = 0;
		link_status.lane_reversed = 0;
		link_status.num_lanes = NUM_LANES;

		link_status.reset();

		bitstream = {};
		collected_flits = {};
		for (int i=0; i < NUM_LANES; i++) begin
			lane_queues[i] = {};
		end
	endfunction :reset_link

	task collect_flits();
		
		flit_t	current_flit;
		partial_flit_t	lane_flit;

		`uvm_info(get_type_name(),$psprintf("starting collect_flits %s", local_config.requester? "Requester" : "Responder"), UVM_HIGH)
		forever begin
			if (link_status.current_state == RESET ) // Reset
				reset_link();
			//-- check if partial flits available
			if (!flit_available())begin
				@(lane_queue_event);//-- wait for any change at the lane queues and recheck flit available before reading the lane queues
			end

			//-- check TS1 sequences
			if (link_status.current_state == TS1) begin
				foreach (lane_queues[i]) begin
				lane_flit = lane_queues[i].pop_front();
					if (lane_flit != 16'b0) begin //-- while TS1 Sequence
						case (i)
							0:	begin
								case (lane_flit[7:4])
									4'h3 : link_status.lane_reversed = 0;
									4'hc : link_status.lane_reversed = 1;
									default : if (local_config.lane_errors_enabled) begin
											`uvm_info(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"), UVM_HIGH)
											//-- cover invalid TS1 sequence error
											current_error = INVALID_TS1;
											collected_packet = new();	
											void'(collected_packet.randomize() with{command == HMC_NULL;});
											hmc_pkt_error_cg.sample();
									end else begin
											`uvm_fatal(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"))
									end
								endcase
								if (!lane_reversal_set) begin
									`uvm_info(get_type_name(), $psprintf("%s Link is %s"
											, local_config.requester?"Requester":"Responder"
											, link_status.lane_reversed?"reversed":"not reversed"
										), UVM_NONE)
								end
								lane_reversal_set = 1;
							end
							NUM_LANES-1: begin
								case (lane_flit[7:4])
									4'h3 : link_status.lane_reversed = 1;
									4'hc : link_status.lane_reversed = 0;
									default : if (local_config.lane_errors_enabled) begin
											`uvm_info(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"), UVM_HIGH)
									end else begin
											`uvm_fatal(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"))
									end
								endcase
							end
							default: begin
									if (local_config.lane_errors_enabled) begin
										if (lane_flit[7:4] != 4'h5)
											`uvm_info(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"), UVM_HIGH)
									end else begin
										if (local_config.lane_errors_enabled) begin
											if (lane_flit[7:4] != 4'h5)
												`uvm_info(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"), UVM_HIGH)
										end
										else begin
											CHK_TS1_ID: assert (lane_flit[7:4] == 4'h5);
										end
									end
							end
						endcase
						if (local_config.lane_errors_enabled) begin
							if (lane_flit[15:8] != 8'hf0)
								`uvm_info(get_type_name(), $psprintf("Detected invalid TS1 sequence on Lane %0d %s", i, local_config.requester?"requester":"responder"), UVM_HIGH)
						end
						else begin
						CHK_UPPER_TS1: assert (lane_flit[15:8] == 8'hf0);
						end
					end
					
					else begin
						hmc_link_cg.sample();
						link_status.first_null_detected = 1;
						null_flits_after_TS1= NUM_LANES/8; //-- add 1 or 2 NULL2 Flits depending on NUM_LANES
					end
				end
			end
			else begin

				for (int j = 0; j < 16; j++) begin //for each bit position in partial flit
					for (int lane = 0; lane < NUM_LANES; lane++) begin //-- for each lane
						bitstream.push_back(lane_queues[link_status.lane_reversed?NUM_LANES-lane-1:lane][0][j]);
					end
				end
				for (int j = 0; j < 16; j++) begin
					void'(lane_queues[j].pop_front());
				end

				while(bitstream.size()>=128) begin //-- at least 1 flit in bitstream
					for (int k = 0; k <128; k++)
						current_flit[k]= bitstream.pop_front();

					if (link_status.current_state == NULL_FLITS_2)
					begin
						link_status.null_after_ts1_seen = 0;
						if (current_flit == 128'h0)
						begin
							null_flits_after_TS1++;
							if(null_flits_after_TS1 >= 32) begin
								link_status.set_null_after_ts1();
							end
							`uvm_info(get_type_name(),$psprintf("null flit #%0d on %s Link",null_flits_after_TS1, local_config.requester?"Requester":"Responder"), UVM_HIGH)
						end
						else begin
							if(null_flits_after_TS1 != 0)
								if(local_config.lane_errors_enabled) begin
									`uvm_info(get_type_name(), $psprintf("received only %d consecutive NULL Flits after TS1 sequences, got %h",null_flits_after_TS1,current_flit  ), UVM_NONE)
									null_flits_after_TS1++;
								end
								else begin
									`uvm_fatal(get_type_name(), $psprintf("received only %d consecutive NULL Flits after TS1 sequences, got %h",null_flits_after_TS1,current_flit  ))
								end
						end
					end
					else if (link_status.current_state == LINK_UP)
					begin
						collected_flits.push_back(current_flit);
						-> flit_queue_event;
					end
				end
			end
		end
	endtask : collect_flits

	function bit check_seq_number(hmc_packet packet);
		check_seq_number = 0;
		if (packet.command != HMC_PRET && packet.command != HMC_IRTRY)  // No sequence numbers to check in PRET
			begin
				if (packet.sequence_number != next_sequence_num) // Sequence error
				begin
					`uvm_info(get_type_name(),
						$psprintf("%s: expected sequence number %0d, got %0d! in packet with cmd %0s, frp %0d and rrp %0d",
							local_config.requester?"Requester":"Responder",next_sequence_num, packet.sequence_number,
							packet.command.name(),packet.forward_retry_pointer, packet.return_retry_pointer),
						UVM_LOW)
					seq_error++;
					current_error = SEQ_ERROR;
					hmc_pkt_error_cg.sample();
					link_status.set_error_abort_mode();
					link_status.clear_irtry_packet_counts();
					check_seq_number = 1;
				end else begin
					`uvm_info(get_type_name(), $psprintf("CMD %s with current seq_nr: %d",packet.command.name(),packet.sequence_number), UVM_HIGH)
					next_sequence_num = packet.sequence_number + 1;
				end
			end
			else // PRET & IRTRY
				if (packet.sequence_number != 0) begin
					`uvm_info(get_type_name(),$psprintf("%s: expected sequence number 0, got %0d! in packet with cmd %0s, frp %0d and rrp %0d",
						local_config.requester?"Requester":"Responder",packet.sequence_number,packet.command.name(),
						packet.forward_retry_pointer, packet.return_retry_pointer),
					UVM_LOW)
					
					seq_error++;
					current_error = SEQ_ERROR;
					hmc_pkt_error_cg.sample();
					link_status.set_error_abort_mode();
					link_status.clear_irtry_packet_counts();
					check_seq_number = 1;
				end
					
	endfunction : check_seq_number
	
	
	function void token_handling(hmc_packet packet);
		
		if (!remote_link_status.relaxed_token_handling) begin
			remote_link_status.token_count += packet.return_token_count; //-- add available token to the remote link
			return_token_port.write(collected_packet);
			if (local_config.requester && packet.return_token_count >0)
			`uvm_info(get_type_name(), $psprintf("Command %s adds %0d tokens to remote, new token count = %0d",
				packet.command.name(), packet.return_token_count,remote_link_status.token_count ),
			UVM_HIGH)
			
		end
		if (!link_status.relaxed_token_handling) begin
			if (packet.get_command_type() != HMC_FLOW_TYPE)// && !packet.poisoned) // Flow packets do not use tokens.
			begin
				if (!local_config.requester)
				`uvm_info(get_type_name(), $psprintf("Tokens available: %d, used tokens: %d, new token count: %d",link_status.token_count,packet.packet_length, link_status.token_count - packet.packet_length), UVM_HIGH)

				if (link_status.token_count < packet.packet_length) //--token underflow must not occur due to the token based flow control
					`uvm_fatal(get_type_name(), $psprintf("send_to_validate: no room to push %s token_count = %0d!", packet.command.name(), link_status.token_count))

				`uvm_info(get_type_name(), $psprintf("send_to_validate: push %s (length %0d) frp %0d token_count %0d new token count %0d.",
					packet.command.name(), packet.packet_length, packet.forward_retry_pointer, link_status.token_count,
					link_status.token_count - packet.packet_length ),
				UVM_HIGH)
				
				link_status.token_count -= packet.packet_length;
				tokens_cg.sample();
			end
		end
	endfunction : token_handling

	function void handle_start_retry(hmc_packet packet);
		if (packet.command == HMC_IRTRY && packet.start_retry) begin
			
			`uvm_info(get_type_name(),$psprintf("received %d start retry IRTRYs for FRP %d",
				link_status.get_StartRetry_packet_count(), packet.return_retry_pointer), UVM_HIGH)
				
			if(link_status.increment_StartRetry_packet_count() >= local_config.irtry_flit_count_received_threshold) begin
				UNEXPECTED_RETRY : assert (remote_link_status.error_abort_mode);

				`uvm_info(get_type_name(),$psprintf("Start Retry Threshold Reached for RRP %d", packet.return_retry_pointer),UVM_NONE)

				if (link_status.get_error_abort_mode()
					&& link_status.irtry_StartRetry_packet_count == local_config.irtry_flit_count_received_threshold)
				begin
					if(remote_link_status.last_successfull_frp != packet.return_retry_pointer)begin
						`uvm_fatal(get_type_name(), $psprintf("expecting RRP %0d, got %0d",
							remote_link_status.last_successfull_frp, packet.return_retry_pointer))
					end
					rrp_port.write(packet.return_retry_pointer);
				end
				start_clear_retry_event.trigger();
			end
		end
		else begin //-- clear start_retry counter
			if (link_status.irtry_StartRetry_packet_count >0) begin
				
				`uvm_info(get_type_name(),$psprintf("clearing Start Retry Counter due to a CMD %s after %0d consecutive StartRetry IRTRYs",
					packet.command.name(), link_status.get_StartRetry_packet_count()),UVM_HIGH)
				
				link_status.irtry_StartRetry_packet_count = 0;
			end
		end
	endfunction : handle_start_retry
	
	function void handle_error_abort_mode(hmc_packet packet);

		if ((packet.clear_error_abort)) begin
			`uvm_info(get_type_name(), $psprintf("Clear Error Abort Mode: %0d",link_status.irtry_ClearErrorAbort_packet_count ), UVM_HIGH)
			if (link_status.increment_ClearErrorAbort_packet_count() == local_config.irtry_flit_count_received_threshold) begin
				link_status.error_abort_mode = 0;

				`uvm_info(get_type_name(), $psprintf("Clearing Error Abort Mode" ), UVM_NONE)
				rrp_port.write(packet.return_retry_pointer); //--commit last valid RRP
			end

		end else begin
			if(!packet.start_retry) begin
				`uvm_info(get_type_name(),$psprintf("clearing Start Retry and Error Abort Counter due to a CMD %s", packet.command.name()),UVM_HIGH)
				link_status.clear_irtry_packet_counts(); //-- reset counter
			end
		end

	endfunction : handle_error_abort_mode

	
	task collect_packets();
		bit				bitstream[];
		flit_t			current_flit;
		flit_t			header_flit;
		bit [31:0]		packet_crc;
		bit [31:0]		calculated_crc;
		int unsigned	current_packet_length;
		int unsigned	last_packet_length;


		`uvm_info(get_type_name(),$psprintf("starting collect_packets "), UVM_HIGH)
		forever begin
			if (link_status.current_state == RESET) //-- reset handling
			begin
				next_sequence_num = 3'b1; //-- reset sequence number 
				packets_after_Link_up = 0;//-- reset packet counter
				@(link_status.current_state);
			end	else
			begin
				if (collected_flits.size() == 0) begin	//-- wait until at least one flit is available
					@(flit_queue_event);
				end
				current_flit = collected_flits.pop_front();	//-- header flit
				
				if (current_flit[5:0] == HMC_NULL) begin //-- do not forward null packets
					null_flits_between_pkts ++;
					if (link_status.irtry_StartRetry_packet_count >0) begin
						`uvm_info(get_type_name(),$psprintf("clearing Start Retry Counter due to a NULL Packet after %0d consecutive StartRetry IRTRYs", link_status.get_StartRetry_packet_count()),UVM_HIGH)
						link_status.irtry_StartRetry_packet_count = 0;
					end
					continue;
				end
				else begin
					//-- if first packet after NULL2
					if (packets_after_Link_up ==0)begin
						null2_cg.sample();
					end
					packets_after_Link_up++;
				end

				//-- check length miss-match
				//-- TODO: include CMD in length check
				if (current_flit[14:11] != current_flit[10:7] || current_flit[14:11] == 0) // Length mismatch or invalid current_packet_length
				begin

					`uvm_info(get_type_name(),$psprintf("%s: current_packet_length mismatch %0x len=%0d, dln = %0d", local_config.requester?"Requester":"Responder", current_flit, current_flit[10:7], current_flit[14:11]),UVM_NONE)
					lng_error ++;
					current_error = LENGTH_ERROR;

					collected_packet = new();	

					if (local_config.lane_errors_enabled)begin 
						void'(collected_packet.randomize() with{
							command == HMC_NULL;
						});
					end else begin
						void'(collected_packet.randomize() with{
							command == hmc_command_encoding'(current_flit[5:0]);
						});
					end
					hmc_pkt_error_cg.sample();

					link_status.set_error_abort_mode();
					link_status.irtry_ClearErrorAbort_packet_count = 0; //-- reset clear error abort count
					//-- ignore packet fragments until first IRTRY 
					while ( (hmc_command_encoding'(current_flit[5:0]) != HMC_IRTRY) 
						|| (current_flit[10:7] != current_flit[14:11])
						|| (current_flit[10:7] !=1) 
					) begin
						if (collected_flits.size() ==0)
							@(flit_queue_event);
						current_flit = collected_flits.pop_front();
					end
				end

				current_packet_length = current_flit[10:7];

				`uvm_info(get_type_name(),$psprintf("%s: current_flit=%0x current_packet_length=%0d", local_config.requester?"Requester":"Responder", current_flit,current_packet_length), UVM_HIGH)

				bitstream = new[current_packet_length*128];

				// pack first flit
				header_flit = current_flit;
				for (int i=0; i<128; i=i+1)
					bitstream[i] = current_flit[i];

				// get and pack the remaining flits
				for (int j=1; j<current_packet_length; j=j+1)
				begin
					if (collected_flits.size() == 0)
						@(collected_flits.size());

					current_flit = collected_flits.pop_front();

					for (int i=0; i<128; i=i+1)
						bitstream[j*128+i] = current_flit[i];
				end

				for (int i = 0; i <32; i++)begin
					packet_crc[i] = bitstream[bitstream.size()-32 +i];
				end
				calculated_crc = collected_packet.calc_crc(bitstream);


				if ( calculated_crc!= packet_crc && !(packet_crc == ~calculated_crc)) begin //-- check CRC
					`uvm_info(get_type_name(), $psprintf("got a CRC error in hmc_packet %x", header_flit), UVM_NONE)
					crc_error ++;
					current_error = CRC_ERROR;
					collected_packet = hmc_packet::type_id::create("collected_packet", this);

					if (local_config.lane_errors_enabled)begin 
						void'(collected_packet.randomize() with{
							command == HMC_NULL;
						});
					end else begin
						void'(collected_packet.unpack(bitstream));
					end
					hmc_pkt_error_cg.sample();

					link_status.set_error_abort_mode();
					link_status.irtry_ClearErrorAbort_packet_count = 0; //-- reset clear error abort count
					continue;

				end


				collected_packet = hmc_packet::type_id::create("collected_packet", this);
				void'(collected_packet.unpack(bitstream));
				if(collected_packet.command != HMC_IRTRY)
				`uvm_info(get_type_name(), $psprintf("collected_packet CMD: %s FRP: %d",
					collected_packet.command.name(), collected_packet.forward_retry_pointer), UVM_HIGH)
				handle_start_retry(collected_packet);

				if (link_status.get_error_abort_mode) begin
					if (collected_packet.command == HMC_IRTRY)
						void'(check_seq_number(collected_packet));
					handle_error_abort_mode(collected_packet);

				end else begin		

					//--check the sequence number
					if(check_seq_number(collected_packet))
						continue;

					//-- at this point each packet should be clean

					token_handling(collected_packet); 

					//-- commit the collected packet
					hmc_packets_cg.sample();
					null_flits_between_pkts = 0;

					if (!link_status.get_error_abort_mode()) begin
						rrp_port.write(collected_packet.return_retry_pointer);

					end

						if (collected_packet.command != HMC_PRET) begin

							if (collected_packet.command != HMC_IRTRY) begin
							frp_port.write(collected_packet);
							link_status.last_successfull_frp = collected_packet.forward_retry_pointer;

							if (collected_packet.poisoned) begin

								`uvm_info(get_type_name(),$psprintf("received a poisoned %s", collected_packet.command.name()), UVM_NONE)
								poisoned_pkt++;
								current_error = POISON;
								hmc_pkt_error_cg.sample();

								continue;
							end

							if (collected_packet.command != HMC_TRET 
								&& !collected_packet.poisoned 
								&& collected_packet.command != HMC_IRTRY 
							) //-- send only Transaction packets 
								item_collected_port.write(collected_packet);
						end
					end
				end
			end
		end
	endtask : collect_packets

	task link_states();
		forever begin
			@({vif.P_RST_N
				,link_status.power_state
				,link_status.all_lanes_locked
				,link_status.all_lanes_alligned
				,link_status.first_null_detected
				,link_status.null_after_ts1_seen}
			);

			casex ({vif.P_RST_N
					,link_status.power_state
					,link_status.all_lanes_locked
					,link_status.all_lanes_alligned
					,link_status.first_null_detected
					,link_status.null_after_ts1_seen})
				6'b0xxxxx :	link_status.current_state = RESET;
				6'b10xxxx :	link_status.current_state = POWER_DOWN;		//-- sleep mode 
				6'b110xxx :	link_status.current_state = PRBS;		//-- scrambler waits for null flits
				6'b1110xx :	link_status.current_state = NULL_FLITS;	//-- scrambler has detected a null flit
				6'b11110x :	link_status.current_state = TS1;			//-- scrambler has detected a TS1 sequence and is in flit sync
				6'b111110 :	link_status.current_state = NULL_FLITS_2;//-- detected first NULL flits after TS1
				6'b111111 :	link_status.current_state = LINK_UP;		//-- Link is UP
			endcase
			`uvm_info(get_type_name(),$psprintf("%s Link current State: %s \t vector: %b",
				local_config.requester?"Requester":"Responder", link_status.current_state.name(),
													{	vif.P_RST_N, 
														link_status.power_state, 
														link_status.all_lanes_locked, 
														link_status.all_lanes_alligned,
														link_status.first_null_detected, 
														link_status.null_after_ts1_seen
													}),UVM_LOW)
			if (link_status.current_state == POWER_DOWN || RESET)
				reset_link();
		end
	endtask : link_states

	task run();
		#1;
		for (int i=0; i<NUM_LANES; i++)
		begin
			automatic int lane = i;
			fork
				`uvm_info(get_type_name(),$psprintf("starting descrambler for Requester lane %0d", lane), UVM_HIGH)
				descramble(lane);
			join_none
		end
		fork
			check_clock();
			monitor_power_pins();
			collect_flits();
			collect_packets();
			link_states();
		join_none

		wait fork;
	endtask : run


	function bit flit_available();
		bit rval = 1'b1;
		// There is only a flit available if all lane_queues are ready

		for (int i=0; i < NUM_LANES; i++)
			rval = rval && lane_queues[i].size()>0;

		return rval;
	endfunction : flit_available
	
	function bit idle_check();
		return transaction_mon.idle_check() 
			&& (link_status.token_count == local_config.requester?link_config.rx_tokens:link_config.hmc_tokens);
	endfunction : idle_check
	
	function void report_phase(uvm_phase phase);
		`uvm_info(get_type_name(),$psprintf("LNG error count  %0d", lng_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("CRC error count  %0d", crc_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("SEQ error count  %0d", seq_error),		UVM_NONE)
		`uvm_info(get_type_name(),$psprintf("poisoned packets %0d", poisoned_pkt),	UVM_NONE)
	endfunction : report_phase

	function void check_phase(uvm_phase phase);
		if (!idle_check())//-- TODO check that all transactions are closed
			`uvm_fatal(get_type_name(),$psprintf("Link is not IDLE"))
	endfunction : check_phase

endclass : hmc_monitor

`endif // HMC_MONITOR_SV
