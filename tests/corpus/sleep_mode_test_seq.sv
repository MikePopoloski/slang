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
// sleep_mode_test sequence
//
//

`ifndef sleep_mode_test_SEQ_SV
`define sleep_mode_test_SEQ_SV

class sleep_mode_test_seq extends hmc_base_seq;

	rand int iterations;
	
	constraint iterations_c {
		iterations >= 1;
		iterations <= 10;
	}

	function new(string name="sleep_mode_test_seq");
		super.new(name);
	endfunction : new


	openhmc_init_seq init;
	hmc_model_init_seq bfm;
	openhmc_check_seq check;
	hmc_base_pkt_seq work;

	reg_openhmc_rf_status_general_c status;
	reg_openhmc_rf_control_c control;
	reg_openhmc_rf_sent_np_c sent_np;
	reg_openhmc_rf_rcvd_rsp_c rcvd_rsp;	

	`uvm_object_utils(sleep_mode_test_seq)
	`uvm_declare_p_sequencer(vseqr)

	hmc_2_axi4_sequence #(.DATA_BYTES(`AXI4BYTES), .TUSER_WIDTH(`AXI4BYTES)) requests;
	int timer;	

	task wait_for_idle ();
		timer = 0;
       	p_sequencer.rf_seqr_hmc.read_reg(status);
       	p_sequencer.rf_seqr_hmc.read_reg(sent_np);
       	p_sequencer.rf_seqr_hmc.read_reg(rcvd_rsp);
       	p_sequencer.rf_seqr_hmc.read_reg(control);
       	#1us;

		while(	((sent_np.fields.cnt_ != rcvd_rsp.fields.cnt_) ||
				(status.fields.hmc_tokens_remaining_ != p_sequencer.link_cfg.hmc_tokens) ||
				(status.fields.rx_tokens_remaining_  != p_sequencer.link_cfg.rx_tokens)) 
				&&
				(timer < 200)) begin
			#1us;
			p_sequencer.rf_seqr_hmc.read_reg(status);
			p_sequencer.rf_seqr_hmc.read_reg(sent_np);
			p_sequencer.rf_seqr_hmc.read_reg(rcvd_rsp);
			`uvm_info(get_type_name(),$psprintf("RX token count in TX_LINK = %0d, should be %0d" , status.fields.rx_tokens_remaining_ , p_sequencer.link_cfg.rx_tokens),UVM_LOW)
			`uvm_info(get_type_name(),$psprintf("HMC token count in TX_LINK = %0d, should be %0d", status.fields.hmc_tokens_remaining_, p_sequencer.link_cfg.hmc_tokens),UVM_LOW)
			`uvm_info(get_type_name(),$psprintf("sent = %0d non-posted packets, received %0d responses", sent_np.fields.cnt_, rcvd_rsp.fields.cnt_),UVM_LOW)
			timer++;
		end
		#3us;
	endtask
	

	virtual task body();
		time sleep_time = 10us;

		`uvm_info(get_type_name(), "starting sleep_mode_test_seq", UVM_NONE)

		//initiate all the registers
		$cast(status,p_sequencer.rf_seqr_hmc.get_by_name("status_general"));
		status.set_check_on_read(1'b0);

		$cast(control,p_sequencer.rf_seqr_hmc.get_by_name("control"));
		control.set_check_on_read(1'b0);

		$cast(sent_np,p_sequencer.rf_seqr_hmc.get_by_name("sent_np"));
		sent_np.set_check_on_read(1'b0);

		$cast(rcvd_rsp,p_sequencer.rf_seqr_hmc.get_by_name("rcvd_rsp"));
		rcvd_rsp.set_check_on_read(1'b0);

		//-- write your test here
		`uvm_do(bfm)
		
		#1us;
        `uvm_do(init)
        #1us;

		repeat (iterations) begin
			repeat(5) begin
				randcase
					1 : `uvm_do_with(work, {req_class == NON_POSTED;})
					1 : `uvm_do_with(work, {req_class == POSTED;})
				endcase
			end
			//Sleep Mode entry and exit
	 		`uvm_info(get_type_name(),$psprintf("SLEEP MODE: WAIT FOR IDLE"),UVM_LOW)
			wait_for_idle();
			`uvm_info(get_type_name(),$psprintf("SLEEP MODE: SET"),UVM_LOW)
			//Set the sleep_mode_test bit within the Register File
			control.fields.set_hmc_sleep_ = 1;
			p_sequencer.rf_seqr_hmc.write_reg(control);
			p_sequencer.rf_seqr_hmc.read_reg(status);
			#1us;
			while(!status.fields.sleep_mode_) begin
				p_sequencer.rf_seqr_hmc.read_reg(status);
			end
			//Stay in Sleep for up to 22 us
			sleep_time_rand_succeeds : assert (std::randomize(sleep_time) 
									with {sleep_time >= 2us && sleep_time < 22us;}); //-- should be 1ms in real system
			#(sleep_time);
			`uvm_info(get_type_name(),$psprintf("SLEEP MODE: EXIT"),UVM_LOW)
			//Force openHMC controller to exit sleep mode
			control.fields.set_hmc_sleep_ = 0;
			p_sequencer.rf_seqr_hmc.write_reg(control);
			while(!status.fields.link_up_) begin
				p_sequencer.rf_seqr_hmc.read_reg(status);
			end
		end

		#1us;
		`uvm_info(get_type_name(), "sleep_mode_test_seq done", UVM_NONE)
		`uvm_do(check)

	endtask : body

endclass : sleep_mode_test_seq

`endif // sleep_mode_test_SEQ_SV
