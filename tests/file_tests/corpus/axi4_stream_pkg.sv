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

`include "axi4_stream_if.sv"
`include "hmc_base_types_pkg.sv"

`timescale 100ps/10ps

package axi4_stream_pkg;

	`include "uvm_macros.svh"
	import uvm_pkg::*;
	import hmc_base_types_pkg::*;
	`include "hmc_module_mon.sv"

	`include "axi4_stream_config.sv"
	

	`include "axi4_stream_valid_cycle.sv"

	`include "axi4_stream_monitor.sv"
	`include "axi4_stream_hmc_monitor.sv"
	

	`include "axi4_stream_master_driver.sv"
	
	`include "tag_handler.sv"
	
	`include "axi4_stream_master_sequencer.sv"
	
	`include "axi4_stream_master_agent.sv"

	`include "axi4_stream_slave_driver.sv"
	`include "axi4_stream_slave_agent.sv"

	`include "axi4_stream_env.sv"
	
	

endpackage : axi4_stream_pkg
