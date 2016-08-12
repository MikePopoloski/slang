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

`ifndef hmc_TB_SV
`define hmc_TB_SV

class hmc_tb #( parameter AXI4_DATA_BYTES=`AXI4BYTES, parameter AXI4_TUSER_WIDTH=`AXI4BYTES) extends uvm_env;
	//-- UVCs

	axi4_stream_env #(
		.DATA_BYTES(AXI4_DATA_BYTES),
		.TUSER_WIDTH(AXI4_TUSER_WIDTH)
		
	) axi4_req;

	axi4_stream_env #(
		.DATA_BYTES(AXI4_DATA_BYTES),
		.TUSER_WIDTH(AXI4_TUSER_WIDTH)
		
	) axi4_rsp;
	

  	hmc_module_env  hmc_module;

	axi4_stream_config axi4_rsp_config;
	axi4_stream_config axi4_req_config;
	
	hmc_link_config link_cfg;

	cag_rgm_rfs_env #(
		.ADDR_WIDTH(`RFS_OPENHMC_RF_AWIDTH),
		.READ_DATA_WIDTH(`RFS_OPENHMC_RF_RWIDTH),
		.WRITE_DATA_WIDTH(`RFS_OPENHMC_RF_WWIDTH)
	) rfs_hmc_I;

	rf_openhmc_rf_c rf_model_hmc;

	vseqr v_seqr;

	int i = 2;

	`uvm_component_param_utils(hmc_tb #(.AXI4_DATA_BYTES(AXI4_DATA_BYTES), .AXI4_TUSER_WIDTH(AXI4_TUSER_WIDTH) ))

	function new (string name="hmc_tb", uvm_component parent=null);
		super.new(name,parent);
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		
		//-- factory overrides

        set_inst_override_by_type("axi4_req.master.sequencer",
			axi4_stream_master_sequencer #( .DATA_BYTES(AXI4_DATA_BYTES), .TUSER_WIDTH(AXI4_TUSER_WIDTH)
										  )::get_type(),
			hmc_2_axi4_sequencer #(	.DATA_BYTES(AXI4_DATA_BYTES),
									.TUSER_WIDTH(AXI4_TUSER_WIDTH)
									)::get_type()
									
		);

		set_inst_override_by_type("hmc_module.axi4_req_mon",
  			hmc_module_mon::get_type(),
  			axi4_stream_hmc_monitor		#(	.DATA_BYTES(AXI4_DATA_BYTES), 
  											.TUSER_WIDTH(AXI4_TUSER_WIDTH))::get_type()
  											
  		);
  		set_inst_override_by_type("hmc_module.axi4_rsp_mon",
  			hmc_module_mon::get_type(),
  			axi4_stream_hmc_monitor		#(	.DATA_BYTES(AXI4_DATA_BYTES), 
  											.TUSER_WIDTH(AXI4_TUSER_WIDTH))::get_type() 
  											
  		);
  		
  		set_inst_override_by_type("hmc_module.hmc_req_mon",hmc_module_mon::get_type(),bfm_2_hmc_mon::get_type());
  		set_inst_override_by_type("hmc_module.hmc_rsp_mon",hmc_module_mon::get_type(),bfm_2_hmc_mon::get_type());
  		
  		
		super.build_phase(phase);


		//-- deploy configuration 
		if (!uvm_config_db#(axi4_stream_config)::get(this, "", "axi4_req_config", axi4_req_config)) begin
			uvm_report_fatal(get_type_name(), $psprintf("axi4_config not set via config_db"));
		end else begin
			uvm_config_db#(axi4_stream_config)::set(this, "axi4_req", "axi4_stream_cfg", axi4_req_config);
		end

		if (!uvm_config_db#(axi4_stream_config)::get(this, "", "axi4_rsp_config", axi4_rsp_config)) begin
			uvm_report_fatal(get_type_name(), $psprintf("axi4_config not set via config_db"));
		end else begin
			uvm_config_db#(axi4_stream_config)::set(this, "axi4_rsp", "axi4_stream_cfg", axi4_rsp_config);
		end

		
		if (!uvm_config_db#(hmc_link_config)::get(this, "", "link_cfg", link_cfg)) begin
			uvm_report_fatal(get_type_name(), $psprintf("hmc_link_config not set via config_db"));
		end else begin
			uvm_config_db#(hmc_link_config)::set(this, "v_seqr", "link_cfg", link_cfg);
			
			uvm_config_db#(hmc_link_config)::set(this, "hmc_module.hmc_req_mon", "link_cfg", link_cfg);
			uvm_config_db#(hmc_link_config)::set(this, "hmc_module.hmc_rsp_mon", "link_cfg", link_cfg);
		end

		//-- create instances
		axi4_req = axi4_stream_env #(.DATA_BYTES(AXI4_DATA_BYTES),.TUSER_WIDTH(AXI4_TUSER_WIDTH))::type_id::create("axi4_req",this);
		axi4_rsp = axi4_stream_env #(.DATA_BYTES(AXI4_DATA_BYTES),.TUSER_WIDTH(AXI4_TUSER_WIDTH))::type_id::create("axi4_rsp",this);

		hmc_module = hmc_module_env::type_id::create("hmc_module",this);

		rfs_hmc_I = cag_rgm_rfs_env #(.ADDR_WIDTH(`RFS_OPENHMC_RF_AWIDTH), .READ_DATA_WIDTH(`RFS_OPENHMC_RF_RWIDTH),.WRITE_DATA_WIDTH(`RFS_OPENHMC_RF_WWIDTH))::type_id::create("rfs_hmc_I", this);
		rf_model_hmc = rf_openhmc_rf_c::type_id::create("rf_model_hmc",this);

		v_seqr = vseqr::type_id::create("v_seqr", this);

	endfunction : build_phase

	function void connect_phase(uvm_phase phase);

        hmc_2_axi4_sequencer #(.DATA_BYTES(AXI4_DATA_BYTES),.TUSER_WIDTH(AXI4_TUSER_WIDTH)) axi4_req_seqr;
        
        axi4_stream_hmc_monitor	#(.DATA_BYTES(AXI4_DATA_BYTES),	.TUSER_WIDTH(AXI4_TUSER_WIDTH)	)  axi4_hmc_req_mon;
        axi4_stream_hmc_monitor	#(.DATA_BYTES(AXI4_DATA_BYTES),	.TUSER_WIDTH(AXI4_TUSER_WIDTH)	)  axi4_hmc_rsp_mon;
        
		bfm_2_hmc_mon	 hmc_rsp_mon;
		bfm_2_hmc_mon	 hmc_req_mon;

		super.connect_phase(phase);
		rfs_hmc_I.assign_vi(tb_top.rfs_hmc_if);
		rfs_hmc_I.set_rf(rf_model_hmc);

		//-- cast sequencer
		if ( !$cast(axi4_req_seqr, axi4_req.master.sequencer))
		`uvm_fatal(get_type_name(), $psprintf("error in seqr cast"));
		
		//-- cast AXI4 to HMC pkt monitors
		if ( !$cast(axi4_hmc_req_mon, hmc_module.axi4_req_mon))
			`uvm_fatal(get_type_name(), $psprintf("error in axi4_req_mon cast"));
		if ( !$cast(axi4_hmc_rsp_mon, hmc_module.axi4_rsp_mon))
			`uvm_fatal(get_type_name(), $psprintf("error in axi4_rsp_mon cast"));
			
		//-- cast BFM to HMC pkt monitors
		if ( !$cast(hmc_req_mon, hmc_module.hmc_req_mon))
			`uvm_fatal(get_type_name(), $psprintf("error in hmc_req_mon cast"));
		if ( !$cast(hmc_rsp_mon, hmc_module.hmc_rsp_mon))
			`uvm_fatal(get_type_name(), $psprintf("error in hmc_rsp_mon scast"));
		
		hmc_rsp_mon.in_mb = tb_top.dut_I.hmc_bfm0.hmc_flit_top.mb_err2driver[0];
		hmc_req_mon.in_mb = tb_top.dut_I.hmc_bfm0.hmc_flit_top.mb_err2retry[0];
		
		
		
		axi4_req.master.sequencer = axi4_req_seqr;
		 
		 
		//-- connect the AXI4 UVC UVM analysis ports to the corresponding Module UVC monitors
		axi4_req.monitor.item_collected_port.connect(axi4_hmc_req_mon.axi4_port);	
		axi4_rsp.monitor.item_collected_port.connect(axi4_hmc_rsp_mon.axi4_port);
		
		//-- connect the AXi4 to HMC pkt response monitor to the tag handler 
		axi4_hmc_rsp_mon.item_collected_port.connect(axi4_req_seqr.handler.hmc_rsp_port);
			
		//-- virtual sequencer
		v_seqr.axi4_req_seqr = axi4_req_seqr;
		v_seqr.rf_seqr_hmc   = rfs_hmc_I.sequencer;
		
		
		v_seqr.scb = hmc_module.scb;
		
	endfunction : connect_phase

endclass : hmc_tb

`endif // hmc_TB_SV
