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

`ifndef BFM_INIT_SEQ
`define BFM_INIT_SEQ

class hmc_model_init_seq extends hmc_base_seq;

	reg_openhmc_rf_status_general_c status;
	reg_openhmc_rf_control_c control;
	reg_openhmc_rf_sent_np_c sent_np;
	reg_openhmc_rf_rcvd_rsp_c rcvd_rsp;

	function new(string name="hmc_model_init_seq");
		super.new(name);
	endfunction : new

	`uvm_object_utils(hmc_model_init_seq)
	`uvm_declare_p_sequencer(vseqr)

	task body();
		
		// init register
		//initiate all the registers (used for sleep mode)
		$cast(status,p_sequencer.rf_seqr_hmc.get_by_name("status_general"));
		status.set_check_on_read(1'b0);

		$cast(control,p_sequencer.rf_seqr_hmc.get_by_name("control"));
		control.set_check_on_read(1'b0);

		$cast(sent_np,p_sequencer.rf_seqr_hmc.get_by_name("sent_np"));
		sent_np.set_check_on_read(1'b0);

		$cast(rcvd_rsp,p_sequencer.rf_seqr_hmc.get_by_name("rcvd_rsp"));
		rcvd_rsp.set_check_on_read(1'b0);

		
		`uvm_info(get_type_name(), $psprintf("Configure BFM"), UVM_NONE)
		`uvm_info(get_type_name(), $psprintf("HMC_Token Count is: %d", p_sequencer.link_cfg.hmc_tokens), UVM_NONE)
		p_sequencer.hmc_link_cfg.cfg_cid                = p_sequencer.link_cfg.cube_id;
        p_sequencer.hmc_link_cfg.cfg_lane_auto_correct  = p_sequencer.link_cfg.cfg_lane_auto_correct;
        p_sequencer.hmc_link_cfg.cfg_rsp_open_loop      = p_sequencer.link_cfg.cfg_rsp_open_loop;

        // These are set to match the design
        p_sequencer.hmc_link_cfg.cfg_rx_clk_ratio       = p_sequencer.link_cfg.cfg_rx_clk_ratio;
        p_sequencer.hmc_link_cfg.cfg_half_link_mode_rx  = p_sequencer.link_cfg.cfg_half_link_mode_rx;
        p_sequencer.hmc_link_cfg.cfg_tx_lane_reverse    = p_sequencer.link_cfg.cfg_tx_lane_reverse;
		p_sequencer.hmc_link_cfg.cfg_tx_lane_delay 		= p_sequencer.link_cfg.cfg_tx_lane_delay;
		
        p_sequencer.hmc_link_cfg.cfg_hsstx_inv          = p_sequencer.link_cfg.cfg_hsstx_inv;
      

        p_sequencer.hmc_link_cfg.cfg_tx_clk_ratio       = p_sequencer.link_cfg.cfg_tx_clk_ratio;
        p_sequencer.hmc_link_cfg.cfg_half_link_mode_tx  = p_sequencer.link_cfg.cfg_half_link_mode_tx;

        p_sequencer.hmc_link_cfg.cfg_descram_enb        = p_sequencer.link_cfg.cfg_scram_enb;     
        p_sequencer.hmc_link_cfg.cfg_scram_enb          = p_sequencer.link_cfg.cfg_scram_enb;                                                                              
        p_sequencer.hmc_link_cfg.cfg_tokens             = p_sequencer.link_cfg.hmc_tokens;          
        p_sequencer.hmc_link_cfg.cfg_tokens_expected    = p_sequencer.link_cfg.rx_tokens;   

        p_sequencer.hmc_link_cfg.cfg_init_retry_rxcnt   = p_sequencer.link_cfg.cfg_init_retry_rxcnt;
        p_sequencer.hmc_link_cfg.cfg_init_retry_txcnt   = p_sequencer.link_cfg.cfg_init_retry_txcnt;
        
        //***Enable Errors - Dont touch
		p_sequencer.hmc_link_cfg.cfg_rsp_dln			= p_sequencer.link_cfg.cfg_rsp_dln;
		p_sequencer.hmc_link_cfg.cfg_rsp_lng			= p_sequencer.link_cfg.cfg_rsp_lng;
		p_sequencer.hmc_link_cfg.cfg_rsp_crc			= p_sequencer.link_cfg.cfg_rsp_crc;
		p_sequencer.hmc_link_cfg.cfg_rsp_seq			= p_sequencer.link_cfg.cfg_rsp_seq;
		p_sequencer.hmc_link_cfg.cfg_rsp_poison			= p_sequencer.link_cfg.cfg_rsp_poison;
        
		p_sequencer.hmc_link_cfg.cfg_req_dln			= p_sequencer.link_cfg.cfg_req_dln;
        p_sequencer.hmc_link_cfg.cfg_req_lng			= p_sequencer.link_cfg.cfg_req_lng;
        p_sequencer.hmc_link_cfg.cfg_req_crc			= p_sequencer.link_cfg.cfg_req_crc;
        p_sequencer.hmc_link_cfg.cfg_req_seq			= p_sequencer.link_cfg.cfg_req_seq;

        //Reduce timings for simulation
        p_sequencer.hmc_link_cfg.cfg_tsref				= p_sequencer.link_cfg.cfg_tsref;
        p_sequencer.hmc_link_cfg.cfg_top				= p_sequencer.link_cfg.cfg_top;  

        p_sequencer.hmc_link_cfg.cfg_retry_timeout      = p_sequencer.link_cfg.cfg_retry_timeout;  
        p_sequencer.hmc_link_cfg.cfg_retry_limit      	= p_sequencer.link_cfg.cfg_retry_limit;  //8

        //Enable retry
        p_sequencer.hmc_link_cfg.cfg_retry_enb          = p_sequencer.link_cfg.cfg_retry_enb;

        if(p_sequencer.hmc_link_cfg.cfg_scram_enb)
            p_sequencer.hmc_link_cfg.cfg_tx_rl_lim      = p_sequencer.link_cfg.cfg_tx_rl_lim;

        p_sequencer.hmc_link_cfg.display(); //uncomment for full link configuration output    

		tb_top.dut_I.hmc_bfm0.set_config(p_sequencer.hmc_link_cfg,0);
		`uvm_info(get_type_name(), $psprintf("HMC BFM CONFIGURATION IS COMPLETE"), UVM_NONE)

		
	endtask : body

endclass : hmc_model_init_seq

`endif // HMC_INIT_SEQ
