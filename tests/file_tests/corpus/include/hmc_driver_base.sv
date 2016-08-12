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
`ifndef HMC_DRIVER_BASE_SV
`define HMC_DRIVER_BASE_SV

class hmc_driver_base#(parameter NUM_LANES = 16) extends uvm_driver #(hmc_packet);


	`uvm_analysis_imp_decl(_hmc_frp)
	uvm_analysis_imp_hmc_frp #(hmc_packet, hmc_driver_base#(.NUM_LANES(NUM_LANES))) hmc_frp_port;

	init_state_t next_state = RESET;
	init_state_t state = RESET;
	init_state_t last_state = LINK_UP;

	virtual interface hmc_sr_if #(.NUM_LANES(NUM_LANES)) vif;

	hmc_token_handler token_handler;
	hmc_retry_buffer  retry_buffer;
	hmc_link_status   remote_status;

	//-- The parameters for this link
	hmc_link_config link_config;

	//-- The parameters for this driver
	hmc_local_link_config local_config;

	//-- Packets to send
	hmc_packet packet_queue[$];

	typedef bit lane_queue [$];
	lane_queue lane_queues [NUM_LANES];	

	event driver_clk;

	uvm_event start_clear_retry_event;

	// Timestamps for debugging
	int reset_timestamp = 0;
	int prbs_timestamp = 0;
	int null_timestamp = 0;
	int req_ts1_timestamp = 0;
	int ts1_timestamp = 0;

	// Timestamps for controlling packet flow
	int last_packet_timestamp = 0;
	int start_retry_timestamp = 0;
	//-- error propability
	int next_poisoned = 0;
	int	lng_error_prob = 0;
	int	seq_error_prob = 0;
	int	crc_error_prob = 0;

	bit recover_from_power_down = 0;

	// Count retry attempts signalled by the responder (from here)
	int retry_attempts = 0;

	// Count retry attempts from the requester
	int remote_retries_signalled = 0;
	int remote_retries_cleared = 0;
	int local_retries_signalled = 0;
	int local_retries_cleared = 0;

	// Internal state for scramblers
	bit [14:0] lfsr[NUM_LANES-1:0];

	// Internal state for packets
	bit [2:0] seq_num = 1;

	// State for tokens and frp
	bit [7:0] frp_queue [$];
	bit [7:0] last_frp = 0;
	bit [7:0] last_rrp;

	int tokens_to_send = 0;

	int used_tokens = 0;
	int sent_tokens = 0;

	bit [14:0] lfsr_seed[0:15] = {
					15'h4D56,
					15'h47FF,
					15'h75B8,
					15'h1E18,
					15'h2E10,
					15'h3EB2,
					15'h4302,
					15'h1380,
					15'h3EB3,
					15'h2769,
					15'h4580,
					15'h5665,
					15'h6318,
					15'h6014,
					15'h077B,
					15'h261F
			};

	bit [15:8]	ts1_high 		= 8'hF0;
	bit [7:4]	ts1_top_lane 	= 4'hC;
	bit [7:4]	ts1_bottom_lane	= 4'h3;
	bit [7:4]	ts1_middle_lane	= 4'h5;

	// Configuration parameters
	bit init_continue;
	bit can_continue;

	`uvm_component_param_utils(hmc_driver_base #(.NUM_LANES(NUM_LANES)))

	function new(string name="hmc_driver_base", uvm_component parent);
		super.new(name,parent);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		vif_found : assert (uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "vif",this.vif));
		config_found : assert (uvm_config_db#(hmc_link_config)::get(this, "", "link_config",link_config));
	endfunction : build_phase

	virtual task run_phase(uvm_phase phase);
		super.run_phase(phase);
	endtask : run_phase

	task reset();

		vif.TXP = {$size(vif.TXP) {1'bz}};
		vif.TXN = {$size(vif.TXN) {1'bz}};
		vif.TXPS = 1'bz;

		seq_num = 1;
		last_rrp = 0;
		init_continue = 0;
		can_continue = 0;
		retry_buffer.reset();

		//-- wait for reset signal
		@(posedge vif.P_RST_N);
		reset_timestamp = $time;

		next_state = INIT;
	endtask : reset

	task clk_gen();
		@(posedge vif.REFCLKP);
		forever begin
			#link_config.bit_time -> driver_clk;
		end
	endtask : clk_gen

	task send_ts1(int ts1_fits);
		bit [4:0] ts1_seq_num;
		bit [NUM_LANES-1:0] fit_val;
		bit [15:0] ts1_values [NUM_LANES-1:0];

		ts1_values[0]		= {ts1_high, ts1_bottom_lane, 4'h0};
		for (int lane=1; lane < local_config.width-1; lane++)
			ts1_values[lane]	= {ts1_high, ts1_middle_lane, 4'h0};
		ts1_values[local_config.width-1]	= {ts1_high, ts1_top_lane, 4'h0};

		//Send some (possibly incomplete) TS1 flits
		while (ts1_fits > 0) begin
			// Cycle through all the sequence numbers
			for (ts1_seq_num=0; ts1_seq_num < 16 && ts1_fits > 0; ts1_seq_num++) begin
				// Add the sequence number to the ts1_values
				for (int i=0; i < local_config.width; i++) begin
					ts1_values[i][3:0] = ts1_seq_num;
				end
				// Send the fits of the ts1 values
				for (int fit=0; fit < 16; fit++) begin
					for (int lane=0; lane < local_config.width; lane++) begin
						fit_val[lane] = ts1_values[lane][fit];
					end
					if (ts1_fits > 0) begin
						drive_fit(fit_val);
					end else begin
						drive_fit({NUM_LANES{1'b0}});
					end
					ts1_fits = ts1_fits - 1;
				end
			end
		end
	endtask : send_ts1

	task initial_trets();
		hmc_packet tret = new();
		//send TRET FLITs
		while (tokens_to_send > 0) begin
			init_tret_randomization : assert (tret.randomize() with {
				command == HMC_TRET;
				poisoned == 0;
				crc_error == 0;
				packet_length == 1;
				duplicate_length == 1;
				return_token_count <= tokens_to_send && return_token_count > 0;
				});
			send_packet(tret);
			tokens_to_send = tokens_to_send - tret.return_token_count;
		end
		next_state = LINK_UP;
	endtask : initial_trets

	task link_up();
		hmc_packet packet;

		get_packets();

		if (packet_queue.size() > 0 && token_handler.tokens_available(packet_queue[0].packet_length) && (250- retry_buffer.get_buffer_used()) > packet_queue[0].packet_length ) begin
			packet = packet_queue.pop_front();	//-- send the first packet in the queue
			if ((next_poisoned < local_config.poisoned_probability))
				send_poisoned(packet);
			else
				send_packet(packet);

			poisoned_propability_randomisation : assert (std::randomize(next_poisoned) with {next_poisoned > 0 && next_poisoned < 1000;});

		end else if ($time-last_packet_timestamp > local_config.send_pret_time && frp_queue.size() > 0) begin
			`uvm_info(get_type_name(),$psprintf("sending pret, frp_queue size = %0d", frp_queue.size()), UVM_HIGH)
			send_pret();
		end else if ($time-last_packet_timestamp > local_config.send_tret_time && (used_tokens - sent_tokens) > 0 &&(250- retry_buffer.get_buffer_used()) >1) begin
			`uvm_info(get_type_name(),$psprintf("sending tret, (<%0d)", used_tokens-sent_tokens), UVM_HIGH)
			send_tret();
		end else begin
			drive_flit(128'h0);
		end

		// From here on, there are no packets being driven.  This is just logic to decide the next state.

		//-- Handle error_abort_mode on remote link 
		if (remote_status.get_error_abort_mode() && $time() - start_retry_timestamp > link_config.retry_timeout_period  ) begin
			next_state = START_RETRY_INIT;
		end
	endtask : link_up

	task start_retry_init();	//-- send start retry IRTRYs

		start_retry_timestamp = $time;
		local_retries_signalled = local_retries_signalled + 1;
		`uvm_info(get_type_name(),$psprintf("sending start retry packets"), UVM_MEDIUM)

		//send IRTRY FLITs
		for (int i=0; i < local_config.irtry_flit_count_to_send; i++)
			send_irtry_start();

		next_state = LINK_UP;
	endtask : start_retry_init

	task clear_retry(); //-- send clear error abort mode IRTRYs

		local_retries_cleared = local_retries_cleared + 1;
		//send IRTRY FLITs
		for (int i=0; i < local_config.irtry_flit_count_to_send; i++)
			send_irtry_clear();
		next_state = SEND_RETRY_PACKETS;
	endtask : clear_retry

	task send_retry_packets();
		hmc_packet packet;
		int spacer_flits;

		packet = retry_buffer.get_retry_packet();
		while (packet != null) begin
			spacer_flits_randomization_succeeds : assert (std::randomize(spacer_flits) with {spacer_flits >= 0 && spacer_flits < 10;});
			for (int i=0; i<spacer_flits; i++) begin
				drive_flit(128'h0);
			end
			retry_send_packet(packet);
			packet = retry_buffer.get_retry_packet();
		end
		next_state = LINK_UP;
	endtask : send_retry_packets

	task get_packets();
		hmc_packet packet;

		if( seq_item_port.has_do_available() ) begin
			if( packet_queue.size() == 0) begin
				seq_item_port.get_next_item(packet);
				packet_queue.push_back(packet);
				seq_item_port.item_done();
			end
		end
	endtask : get_packets

	task send_irtry_start();
		send_irtry(1,0);
	endtask : send_irtry_start

	task send_irtry_clear();
		send_irtry(0,1);
	endtask : send_irtry_clear

	task send_irtry(input bit start, input bit clear);
		hmc_packet irtry = new();

		irtry_randomization: assert (irtry.randomize() with {
			command == HMC_IRTRY;
			packet_length == 1;
			duplicate_length == 1;
			start_retry == start;
			clear_error_abort == clear;
		});

		send_packet(irtry);
	endtask : send_irtry

	task send_tret();

		hmc_packet tret = new();

		tret_randomization: assert (tret.randomize() with {
			command == HMC_TRET;
			packet_length == 1;
			duplicate_length == 1;
		});

		send_packet(tret);

	endtask : send_tret

	task send_pret();

		hmc_packet pret = new();

		pret_randomization: assert (pret.randomize() with {
			command == HMC_PRET;
			packet_length == 1;
			duplicate_length == 1;
		});

		send_packet(pret);

	endtask : send_pret

	task send_poisoned(input hmc_packet pkt);		
		hmc_packet poisoned = new pkt; //-- copy the pkt into a new one 
		
		`uvm_info(get_type_name(),$psprintf("Poisoning Packet with command %s and tag %d", poisoned.command.name(), poisoned.tag),UVM_NONE)

		poisoned.poisoned = 1;
		send_packet(poisoned);
		
		packet_queue.push_back(pkt);//-- resent the packet later

	endtask : send_poisoned

	task send_packet(input hmc_packet pkt);
		int packet_frp;
		bit [31:0] crc;
		int bit_pos;
		int tok_cnt;
		// Save packet in Retry buffer if not IRTRY, NULL, or PRET
		// Tokens and Sequence numbers are saved in the retry buffer.
		
		if (pkt.command == HMC_IRTRY ||
			pkt.command == HMC_NULL ||
			pkt.command == HMC_PRET) begin
			packet_frp = 0;
			pkt.sequence_number = 0;
			retry_send_packet(pkt);
		end else begin
			pkt.sequence_number = seq_num;
			if (state != INITIAL_TRETS) begin
				if (used_tokens - sent_tokens > 0) begin
					// Always send tokens with TRETs
					if (pkt.command == HMC_TRET)
						tok_cnd_tret_randomization : assert (std::randomize(tok_cnt) with {(pkt.command == HMC_TRET && tok_cnt > 0)  && tok_cnt < 32 && tok_cnt <= (used_tokens - sent_tokens);}); 
					else
						tok_cnt_randomization_succeeds : assert (std::randomize(tok_cnt) with {(tok_cnt >= 0) && tok_cnt < 32 && tok_cnt <= (used_tokens - sent_tokens);});
					pkt.return_token_count = tok_cnt;
				end else begin
					pkt.return_token_count = 0;
				end
			end
			packet_frp = retry_buffer.add_packet(pkt);
			if(packet_frp != -1)begin
				seq_num++;
				if (state != INITIAL_TRETS) begin
					sent_tokens += pkt.return_token_count;
				end
				// From now on, it's equivalent to retry
				`uvm_info(get_type_name(), $psprintf("Sending CDM  %s with TRETS %d", pkt.command.name(), pkt.return_token_count), UVM_HIGH)
				retry_send_packet(pkt);
			end
		end
	endtask : send_packet

	task retry_send_packet(input hmc_packet pkt);
		bit [31:0] crc;
		int bit_pos;
		int bit_error;
		int error_type;
		int rrp_to_send;
		
		
		int pkt_lng;
		bit [2:0]seq_number;
	

		// Don't change the stored packet (except to clear the CRC error flag)
		hmc_packet copy = new pkt;
		
		// Return retry pointers are not saved.
		// Skip some retry pointers
		rrp_to_send_randomization_succeeds : assert (std::randomize(rrp_to_send) with {rrp_to_send >= 0 && rrp_to_send <= frp_queue.size();});
		if (rrp_to_send == 0) begin
			copy.return_retry_pointer = last_rrp;
		end else begin
			for (int i=0;i<rrp_to_send;i++) begin
				copy.return_retry_pointer = frp_queue.pop_front();
				`uvm_info(get_type_name(),$psprintf("popped %0d for frp in %s", copy.return_retry_pointer, copy.command.name()),UVM_HIGH)
			end
		end
		last_rrp = copy.return_retry_pointer;

		//-- ERROR INJECTION

		//-- adding sequence error
		error_type_seq_error_randomization : assert (std::randomize(seq_error_prob) with {seq_error_prob > 0 && seq_error_prob < 1000;});
		if (seq_error_prob < local_config.seq_error_probability) begin
				randcase
					1: 	copy.sequence_number = copy.sequence_number + 1;
					1:	copy.sequence_number = copy.sequence_number - 1;
					1:	begin
							random_SEQ_succeeds : assert(
									std::randomize(seq_number) with { seq_number !=copy.sequence_number;}); 
							copy.sequence_number = seq_number; 
						end
				endcase
				`uvm_info(get_type_name(),$psprintf("injecting SEQ error in CMD %s and FRP %d",copy.command.name(), copy.forward_retry_pointer), UVM_NONE)
		end

			
		//-- inserting Length Error
		error_type_lng_error_randomization : assert (std::randomize(lng_error_prob) with {lng_error_prob > 0 && lng_error_prob < 1000;});
		if (lng_error_prob < local_config.lng_error_probability) begin
			randcase
				1:	copy.packet_length = copy.packet_length + 1;
				1:	copy.packet_length = copy.packet_length - 1;
				1:	copy.duplicate_length = copy.duplicate_length + 1;
				1:	copy.duplicate_length = copy.duplicate_length - 1;
				1:	begin 	random_LNG_succeeds : assert(
								std::randomize(pkt_lng) with {pkt_lng >= 0 && pkt_lng < 16  && pkt_lng !=copy.packet_length;}); 
							copy.packet_length = pkt_lng; 
					end
				1:	begin	random_DLN_succeeds : assert(
								std::randomize(pkt_lng) with {pkt_lng >= 0 && pkt_lng < 16  && pkt_lng !=copy.duplicate_length;});
							copy.duplicate_length = pkt_lng; 
					end
			endcase
		end
			
		crc = copy.calculate_crc(); //-- calculate crc for packet with valid tail
		
		
		//-- poisoning packets
		if (copy.poisoned) begin
			`uvm_info(get_type_name(),$psprintf("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX poisoning packet with CRC %0x and CMD %s and TAG %d", ~crc, copy.command.name(), copy.tag),UVM_LOW)
			crc = ~crc;
		end


		//-- inserting CRC error
		error_type_crc_error_randomization : assert (std::randomize(crc_error_prob) with {crc_error_prob > 0 && crc_error_prob < 1000;});
		if (crc_error_prob < local_config.crc_error_probability * copy.packet_length) begin //-- increase the crc error probability for longer packets
			int clear_crc_error;
			crc_bit_error_randomization_succeeds : assert (std::randomize(bit_pos) with {bit_pos >= 0 && bit_pos < 32;});
			`uvm_info(get_type_name(),$psprintf("inserting crc error at %0x", bit_pos),UVM_LOW)
			crc[bit_pos] = !crc[bit_pos];
			clear_crc_error_randomization_succeeds : assert (std::randomize(clear_crc_error) with {clear_crc_error >= 0 && clear_crc_error < 3;});
			if (clear_crc_error == 1)
				pkt.crc_error = 0;
		end
		copy.packet_crc = crc;
		drive_tx_packet(copy);

	endtask : retry_send_packet

	task drive_fit(input bit[NUM_LANES-1:0] new_value);
		if (link_config.scramblers_enabled) begin
			drive_lanes(get_scrambler_value()^new_value);
		end else begin 
			drive_lanes(new_value);
		end
		@driver_clk;
		step_scramblers();
	endtask : drive_fit

	task drive_flit(input bit [127:0] flit);
		int i;
		bit [15:0] fits [16];

		for (int i=0; i<128; i++)
			fits[i/local_config.width][i%local_config.width] = flit[i];

		for (int i=0; i<128/local_config.width;i++) begin
			drive_fit(fits[i]);
		end

	endtask : drive_flit

	task drive_tx_packet(input hmc_packet pkt);
		bit bitstream[];
		bit [127:0] flits [9]; // Max packet size is 9 flits
		bit [127:0] curr_flit;
		int i;
		int bitcount;
		bitcount = pkt.pack(bitstream);

		for (int i=0; i<bitcount; i++)
			flits[i/128][i%128] = bitstream[i];
		for (int i=0; i<bitcount/128; i++) begin
			drive_flit(flits[i]);
		end

		last_packet_timestamp = $time;

	endtask : drive_tx_packet

	virtual function void drive_lanes(input bit[NUM_LANES-1:0] new_value);
		`uvm_info(get_type_name(),$psprintf("called virtual function drive_lanes!"), UVM_HIGH)
	endfunction : drive_lanes

	function void reset_lfsr();
		int i;

		for (i = 0; i < NUM_LANES; i= i+1) begin
			if (local_config.reverse_lanes == 1)
				lfsr[i] = lfsr_seed[NUM_LANES-1-i];
			else
				lfsr[i] = lfsr_seed[i];
		end
	endfunction : reset_lfsr

	function void step_scramblers();
		int i;

		if (link_config.scramblers_enabled) begin
			for (i = 0; i < NUM_LANES; i= i+1) begin
				lfsr[i] = {lfsr[i][1]^lfsr[i][0], lfsr[i][14:1]};
			end
		end
	endfunction : step_scramblers

	function bit[NUM_LANES-1:0] get_scrambler_value();
		int i;

		if (link_config.scramblers_enabled) begin
			for (i = 0; i < NUM_LANES; i= i+1) begin
				get_scrambler_value[i] = lfsr[i][0];
			end
		end else begin
			for (i = 0; i < NUM_LANES; i= i+1) begin
				get_scrambler_value = {NUM_LANES {1'b0}};
			end
		end
	endfunction : get_scrambler_value

	// I2C or JTAG would configure the HMC during reset
	function void set_init_continue();
		tb_respects_tINIT : assert (can_continue);
		init_continue = 1;
	endfunction : set_init_continue

	virtual function void write_hmc_frp(input hmc_packet pkt);

		bit [7:0] frp;
		int random_wait;

		`uvm_info(get_type_name(),$psprintf("hmc_frp: %s with FRP %0d & size %0d",pkt.command.name(), pkt.forward_retry_pointer, pkt.packet_length),UVM_HIGH)

		// IRTRY and PRET do not have valid frp fields
		if (pkt.command != HMC_IRTRY && pkt.command != HMC_PRET) begin
			frp = pkt.forward_retry_pointer;
			if (frp != last_frp) begin
				frp_queue.push_back(frp);
				last_frp = frp;
			end
		end

		if (pkt.get_command_type != HMC_FLOW_TYPE && !pkt.poisoned ) begin
			used_tokens_does_not_overflow : assert ( used_tokens < used_tokens + pkt.packet_length);
			used_tokens = used_tokens + pkt.packet_length;
		end

	endfunction : write_hmc_frp

endclass : hmc_driver_base

`endif // HMC_DRIVER_BASE_SV

