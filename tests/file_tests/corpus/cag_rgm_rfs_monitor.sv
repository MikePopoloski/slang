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
// cag rgm rfs monitor OVC monitor
//
//

`ifndef CAG_RGM_RFS_MONITOR_SV
`define CAG_RGM_RFS_MONITOR_SV

class cag_rgm_rfs_monitor #(
		parameter ADDR_WIDTH       = 6,
		parameter READ_DATA_WIDTH  = 64,
		parameter WRITE_DATA_WIDTH = 64
	) extends uvm_monitor;

	uvm_analysis_port #(cag_rgm_transfer) request_port;
	uvm_analysis_port #(cag_rgm_transfer) response_port;

	virtual cag_rgm_rfs_if #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.READ_DATA_WIDTH(READ_DATA_WIDTH),
		.WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)
	) rfs_if;

	cag_rgm_transfer collected_request;
	cag_rgm_transfer collected_response;

	bit	enable_coverage		= 1;
	bit	enable_checks		= 1;

	int	cycles_between_req	= 0;
	int	cycles_between_resp	= 0;

	`uvm_component_param_utils_begin(cag_rgm_rfs_monitor #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)))
		`uvm_field_int(enable_coverage, UVM_ALL_ON)
		`uvm_field_int(enable_checks, UVM_ALL_ON)
	`uvm_component_utils_end

	function new ( string name="cag_rgm_rfs_monitor", uvm_component parent );
		super.new(name, parent);
		request_port	= new("request_port", this);
		response_port	= new("response_port", this);
	endfunction : new


	function void assign_vi( virtual interface cag_rgm_rfs_if #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)) rfs_if );
		this.rfs_if	= rfs_if;
	endfunction : assign_vi


	task run();
		#1;
		do_reset();
		fork
			collect_request_transfers();
			collect_response_transfers();
		join_none
	endtask : run


	task do_reset();
		while (rfs_if.res_n == 0)
			@( posedge rfs_if.clk );
	endtask : do_reset


	task collect_request_transfers();

		forever
		begin
			cycles_between_req				= 0;

			// wait for write or read enable
			while (!(rfs_if.wen || rfs_if.ren)) begin
				cycles_between_req++;
				@(posedge rfs_if.clk);
			end

			collected_request				= cag_rgm_transfer::type_id::create("collected_request", this);
			if(recording_detail == UVM_FULL)
				collected_request.enable_recording({get_full_name(),"_request"});
			void'(collected_request.begin_tr());

			if (rfs_if.ren)
				collected_request.command	= CAG_RGM_READ;
			else
				collected_request.command	= CAG_RGM_WRITE;

			collected_request.address		= {{64-3-ADDR_WIDTH {1'b0}}, rfs_if.address,3'b0};
			collected_request.data			= rfs_if.write_data;
			collected_request.delay			= cycles_between_req;
			collected_request.error			= 1'b0;

			@(posedge rfs_if.clk);

			if (enable_checks)
				perform_request_checks();
			if (enable_coverage)
				perform_request_coverage();

			void'(collected_request.end_tr());
			// forward the collected_request to the next higher layer of the verification environment
//			collected_request.print();
			request_port.write(collected_request);
		end
	endtask : collect_request_transfers


	task collect_response_transfers();

		forever begin
			cycles_between_resp = 0;

			while (!(rfs_if.wen || rfs_if.ren)) begin
				@(posedge rfs_if.clk);
			end

			collected_response = cag_rgm_transfer::type_id::create("collected_response", this);

			if(rfs_if.wen)
				collected_response.command = CAG_RGM_WRITE_RESPONSE;
			else
				collected_response.command = CAG_RGM_READ_RESPONSE;

			// wait for write or read enable
			while (!rfs_if.access_done)	begin
				cycles_between_resp++;
				@(posedge rfs_if.clk);
			end

			if(recording_detail == UVM_FULL)
				collected_response.enable_recording({get_full_name(),"_response"});
			void'(collected_response.begin_tr());

			collected_response.address = {{64-ADDR_WIDTH {1'b0}}, rfs_if.address}; //-- FIXME? address should be byte aligned? not qw?
			collected_response.data    = rfs_if.read_data;
			collected_response.delay   = cycles_between_req;
			collected_response.error   = rfs_if.invalid_address;

			@(posedge rfs_if.clk);

			if (enable_checks)
				perform_response_checks();
			if (enable_coverage)
				perform_response_coverage();

			void'(collected_response.end_tr());
			// forward the collected_response to the next higher layer of the verification environment
//			collected_response.print();
			response_port.write(collected_response);
		end
	endtask : collect_response_transfers


	// checks
	function void perform_request_checks();
		// perform data checks on collected_packet
	endfunction : perform_request_checks

	function void perform_response_checks();
		//-- perform data checks on collected_packet
		if(collected_response.error)
			uvm_report_fatal(get_type_name(),$psprintf("Invalid access to address 0x%0h",collected_response.address));
	endfunction : perform_response_checks


	// coverage
	function void perform_request_coverage();
		// perform coverage on collected_packet
	endfunction : perform_request_coverage

	function void perform_response_coverage();
		// perform coverage on collected_packet
	endfunction : perform_response_coverage

endclass : cag_rgm_rfs_monitor

`endif // CAG_RGM_RFS_MONITOR_SV
