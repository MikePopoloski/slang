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

`ifndef HMC_INIT_SEQ
`define HMC_INIT_SEQ

class openhmc_init_seq extends hmc_base_seq;

	function new(string name="openhmc_init_seq");
		super.new(name);
	endfunction : new

	`uvm_object_utils(openhmc_init_seq)
	`uvm_declare_p_sequencer(vseqr)

	bit phy_tx_ready 	= 1'b0;
	bit phy_rx_ready 	= 1'b0;
	bit link_up 		= 1'b0;
	int timeout 		= 0;

	task body();

		//------------------------------------------------------- configure the openHMC controller
		reg_openhmc_rf_control_c 		control;
		reg_openhmc_rf_status_general_c status;
		reg_openhmc_rf_status_init_c 	status_init;
		reg_openhmc_rf_counter_reset_c 	cnt_reset;

		`uvm_info(get_type_name(), "Running init sequence", UVM_NONE)

		$cast(control,p_sequencer.rf_seqr_hmc.get_by_name("control"));
		control.set_check_on_read(1'b0);
		p_sequencer.rf_seqr_hmc.read_reg(control);

		control.fields.rx_token_count_ 		= p_sequencer.link_cfg.rx_tokens;
		control.fields.scrambler_disable_ 	= ~p_sequencer.link_cfg.cfg_scram_enb;
		control.fields.bit_slip_time_ 		= p_sequencer.link_cfg.bit_slip_time;
		control.fields.set_hmc_sleep_ 		= 0;
		control.fields.run_length_enable_ 	= ~p_sequencer.link_cfg.cfg_scram_enb;
		control.fields.irtry_to_send_ 		= p_sequencer.link_cfg.cfg_init_retry_txcnt*4;
		control.fields.irtry_received_threshold_ = p_sequencer.link_cfg.cfg_init_retry_rxcnt;

		p_sequencer.rf_seqr_hmc.write_reg(control);

		//Dummy Read to status init
		$cast(status_init,p_sequencer.rf_seqr_hmc.get_by_name("status_init"));
		status_init.set_check_on_read(1'b0);
		p_sequencer.rf_seqr_hmc.read_reg(status_init);

		//Dummy counter reset
		$cast(cnt_reset,p_sequencer.rf_seqr_hmc.get_by_name("counter_reset"));
		cnt_reset.fields.rreinit_ = 1;
		p_sequencer.rf_seqr_hmc.write_reg(cnt_reset);

		//-- Wait until the PHY is out of reset
		$cast(status,p_sequencer.rf_seqr_hmc.get_by_name("status_general"));
		status.set_check_on_read(1'b0);
		while (phy_tx_ready == 1'b0)
		begin
			#1us;
			p_sequencer.rf_seqr_hmc.read_reg(status);
			phy_tx_ready = status.fields.phy_tx_ready_;
			`uvm_info(get_type_name(), "Waiting for the PHY TX to get ready", UVM_NONE)
		end
		`uvm_info(get_type_name(), "Phy TX ready", UVM_NONE)

		//------------------------------------------------------- Set Reset and Init Continue
		control.fields.p_rst_n_ = 1;
		p_sequencer.rf_seqr_hmc.write_reg(control);
		#1us;

		control.fields.hmc_init_cont_set_ = 1;
		p_sequencer.rf_seqr_hmc.write_reg(control);
		`uvm_info(get_type_name(), "Init cont in RF set", UVM_NONE)

		//------------------------------------------------------- Wait for the PHY to get ready
		while (phy_rx_ready == 1'b0)
		begin
			#1us;
			p_sequencer.rf_seqr_hmc.read_reg(status);
			phy_rx_ready = status.fields.phy_rx_ready_;
			`uvm_info(get_type_name(), "Waiting for PHY RX to get ready", UVM_NONE)
		end
		`uvm_info(get_type_name(), "Phy RX is ready", UVM_NONE)

		//-- Poll on link_up to make sure that it comes up.
		while (link_up == 1'b0)
		begin
			if (timeout == 8000) //-- Try Resetting it.
			begin
				`uvm_fatal(get_type_name(), "The link didn't come up...")
			end
			#4ns;
			p_sequencer.rf_seqr_hmc.read_reg(status);
			link_up = status.fields.link_up_;
			timeout = timeout + 1;
		end
		`uvm_info(get_type_name(), "Link is UP !", UVM_NONE)

	endtask : body

endclass : openhmc_init_seq

`endif // HMC_INIT_SEQ
