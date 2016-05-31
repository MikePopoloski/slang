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
// cag rgm rfs driver
//
//

`ifndef CAG_RGM_RFS_DRIVER_SV
`define CAG_RGM_RFS_DRIVER_SV

class cag_rgm_rfs_driver #(
		parameter ADDR_WIDTH       = 6,
		parameter READ_DATA_WIDTH  = 64,
		parameter WRITE_DATA_WIDTH = 64
	) extends uvm_driver #(cag_rgm_transfer);

    virtual cag_rgm_rfs_if #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.READ_DATA_WIDTH(READ_DATA_WIDTH),
		.WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)
	) rfs_if;

	cag_rgm_transfer rgm_item;

	`uvm_component_param_utils(cag_rgm_rfs_driver #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)))

	function new (string name="cag_rgm_rfs_driver", uvm_component parent);
		super.new(name, parent);
	endfunction : new

	function void build();
		super.build();
	endfunction : build

	function void assign_vi(virtual interface cag_rgm_rfs_if #(.ADDR_WIDTH(ADDR_WIDTH), .READ_DATA_WIDTH(READ_DATA_WIDTH), .WRITE_DATA_WIDTH(WRITE_DATA_WIDTH)) rfs_if);
		this.rfs_if = rfs_if;
	endfunction : assign_vi

	task do_reset();
		rfs_if.address		<= {ADDR_WIDTH {1'b0}};
		rfs_if.wen			<= 1'b0;
		rfs_if.ren			<= 1'b0;
		rfs_if.write_data	<= {WRITE_DATA_WIDTH {1'b0}};

		while (rfs_if.res_n == 0)
			@( posedge rfs_if.clk );

	endtask : do_reset

	task run();
		#1;
		do_reset();

		forever
		begin
			if (rfs_if.res_n == 0)
				do_reset();

			seq_item_port.get_next_item(rgm_item);
			drive_item();
			seq_item_port.item_done();
		end
	endtask : run


	task drive_item();

		//uvm_report_info(get_type_name(), $psprintf("start sending rgm_item:\n%s",rgm_item.sprint()));
		// Start sending:
		@(posedge rfs_if.clk);

		// Wait until start delay is over
		repeat (rgm_item.delay)
			@(posedge rfs_if.clk);

		// start request
		rfs_if.address		<= rgm_item.address[3+(ADDR_WIDTH-1):3];
		rfs_if.write_data	<= rgm_item.data;
		rfs_if.wen			<= (rgm_item.command == CAG_RGM_WRITE);
		rfs_if.ren			<= (rgm_item.command == CAG_RGM_READ);

		@(posedge rfs_if.clk);
		rfs_if.wen			<= 1'b0;
		rfs_if.ren			<= 1'b0;

		while (rfs_if.access_done == 0)
			@(posedge rfs_if.clk);

		@(posedge rfs_if.clk);
		// end request
		rfs_if.address		<= {ADDR_WIDTH {1'b0}};
		rfs_if.write_data	<= {WRITE_DATA_WIDTH {1'b0}};

	endtask : drive_item

endclass : cag_rgm_rfs_driver

`endif // CAG_RGM_RFS_DRIVER_SV
