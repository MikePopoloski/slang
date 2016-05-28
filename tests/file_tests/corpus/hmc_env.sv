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
`ifndef HMC_ENV_SV
`define HMC_ENV_SV



class hmc_env #(parameter NUM_LANES = 16) extends uvm_env;
	
	hmc_link_config link_config;
	
	virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)) vif;
	virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)) int_vif;
		
	hmc_error_injector #(.NUM_LANES(NUM_LANES)) req_inj;
	hmc_error_injector #(.NUM_LANES(NUM_LANES)) rsp_inj;
	
	
	hmc_status h_status;	
	hmc_monitor #(.NUM_LANES(NUM_LANES)) req_mon;
	hmc_monitor #(.NUM_LANES(NUM_LANES)) rsp_mon;
		
	
	hmc_transaction_mon req_transaction_mon;
	hmc_transaction_mon rsp_transaction_mon;
	
	hmc_tag_mon tag_mon;
	
	hmc_requester_agent #(.NUM_LANES(NUM_LANES)) requester;
	hmc_responder_agent #(.NUM_LANES(NUM_LANES)) responder;

	`uvm_component_param_utils(hmc_env #(.NUM_LANES(NUM_LANES)))
	
	function new(string name="hmc_env", uvm_component parent);
		super.new(name,parent);
		h_status = new("h_status",this);
	endfunction : new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "vif",vif) ) begin
			this.vif = vif;
			
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "req_inj","ext_vif",vif);
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "rsp_inj","ext_vif",vif);
			
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "rsp_mon","vif",vif);
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "rsp_mon.cdr","vif",vif);
			
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "requester","vif",vif);
		end else begin
			`uvm_fatal(get_type_name(),"vif is not set")	
		end
		
		if(uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::get(this, "", "int_vif",int_vif) ) begin
			this.int_vif = int_vif;

			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "req_inj","int_vif",int_vif);
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "rsp_inj","int_vif",int_vif);

			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "req_mon","vif",int_vif);
			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "req_mon.cdr","vif",int_vif);

			uvm_config_db#(virtual interface hmc_sr_if#(.NUM_LANES(NUM_LANES)))::set(this, "responder","vif",int_vif);
		end

		req_inj = hmc_error_injector#(.NUM_LANES(NUM_LANES))::type_id::create("req_inj", this);
		req_inj = hmc_error_injector#(.NUM_LANES(NUM_LANES))::type_id::create("rsp_inj", this);

		req_mon = hmc_monitor#(.NUM_LANES(NUM_LANES))::type_id::create("req_mon", this);
		rsp_mon = hmc_monitor#(.NUM_LANES(NUM_LANES))::type_id::create("rsp_mon", this);

		uvm_config_db#(hmc_status)::set(this, "requester", "h_status", h_status);
		uvm_config_db#(hmc_status)::set(this, "responder", "h_status", h_status);

		uvm_config_db#(hmc_status)::set(this, "req_mon", "status", h_status);
		uvm_config_db#(hmc_status)::set(this, "rsp_mon", "status", h_status);
		
		uvm_config_db#(hmc_link_status)::set(this, "req_inj", "link_status", h_status.Requester_link_status);
		uvm_config_db#(hmc_link_status)::set(this, "rsp_inj", "link_status", h_status.Responder_link_status);

        if (uvm_config_db#(hmc_link_config)::get(this, "", "link_config", link_config)) begin
	        if(link_config.enable_tag_checking)
	        	tag_mon = hmc_tag_mon::type_id::create("tag_mon", this);

	        set_config_int("req_transaction_mon", "enable_tag_checking", link_config.enable_tag_checking);
			set_config_int("rsp_transaction_mon", "enable_tag_checking", link_config.enable_tag_checking);

			req_transaction_mon = hmc_transaction_mon::type_id::create("req_transaction_mon", this);
			rsp_transaction_mon = hmc_transaction_mon::type_id::create("rsp_transaction_mon", this);

	        uvm_config_db#(hmc_link_config)::set(this, "rsp_mon.cdr","link_config",link_config);
	        uvm_config_db#(hmc_link_config)::set(this, "req_mon.cdr","link_config",link_config);

			uvm_config_db#(hmc_link_config)::set(this, "req_mon", "link_config", link_config);
	        uvm_config_db#(hmc_link_config)::set(this, "rsp_mon", "link_config", link_config);

	        uvm_config_db#(hmc_local_link_config)::set(this, "req_mon", "local_config", link_config.requester);
	        uvm_config_db#(hmc_local_link_config)::set(this, "rsp_mon", "local_config", link_config.responder);

	        uvm_config_db#(hmc_link_config)::set(this, "req_inj", "link_config", link_config);
	        uvm_config_db#(hmc_link_config)::set(this, "rsp_inj", "link_config", link_config);

	        uvm_config_db#(hmc_local_link_config)::set(this, "req_inj", "local_config", link_config.requester);
	        uvm_config_db#(hmc_local_link_config)::set(this, "rsp_inj", "local_config", link_config.responder);

        	uvm_config_db#(hmc_link_config)::set(this, "requester.driver", "link_config", link_config);
        	uvm_config_db#(hmc_link_config)::set(this, "responder.driver", "link_config", link_config);
        end
		else begin
			uvm_report_fatal(get_type_name(), $psprintf("link_config not set via config_db"));
		end

		set_config_int("requester", "active_passive", link_config.requester.active);
		set_config_int("responder", "active_passive", link_config.responder.active);
		
		requester = hmc_requester_agent#(.NUM_LANES(NUM_LANES))::type_id::create("requester",this);
		responder = hmc_responder_agent#(.NUM_LANES(NUM_LANES))::type_id::create("responder",this);
		
		requester.monitor = rsp_mon;
		responder.monitor = req_mon;
		
		responder.req_transaction_mon = req_transaction_mon;
		
		if(link_config.enable_tag_checking == UVM_ACTIVE) begin
			rsp_transaction_mon.tag_mon = tag_mon;
			req_transaction_mon.tag_mon = tag_mon;
		end
		
		req_mon.transaction_mon = rsp_transaction_mon;
		rsp_mon.transaction_mon = req_transaction_mon;
	endfunction : build_phase

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);

		req_mon.return_token_port.connect(req_transaction_mon.pkt_import);
		rsp_mon.return_token_port.connect(rsp_transaction_mon.pkt_import);

		req_mon.rrp_port.connect(rsp_transaction_mon.rrp_import);
		rsp_mon.rrp_port.connect(req_transaction_mon.rrp_import);
	endfunction : connect_phase
	
endclass : hmc_env

`endif // HMC_ENV_SV
