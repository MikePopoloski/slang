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

`include "hmc_sr_if.sv"
//`include "hmc_base_types_pkg.sv"

`timescale 1ps/1ps

package hmc_pkg;
	
	`include "uvm_macros.svh"
	import uvm_pkg::*;
	import hmc_base_types_pkg::*;
	
	typedef enum {
		REQUESTER,
		RESPONDER
	} link_type_t;

	`include "hmc_config.sv"
	`include "hmc_tag_mon.sv"
	`include "hmc_transaction_mon.sv"
	
	`include "hmc_link_status.sv"
	
	
	`include "hmc_status.sv"
	`include "hmc_cdr.sv"
	
	`include "hmc_monitor.sv"
	`include "hmc_error_injector.sv"
	
	`include "hmc_token_handler.sv"
	`include "hmc_retry_buffer.sv"
	
	`include "hmc_driver_base.sv"

	`include "hmc_requester_driver.sv"
	`include "hmc_requester_sequencer.sv"
	`include "hmc_requester_sequence.sv"
	`include "hmc_requester_agent.sv"

	`include "hmc_responder_driver.sv"
	`include "hmc_responder_sequencer.sv"
	`include "hmc_responder_sequence.sv"
	`include "hmc_responder_agent.sv"
	
	
	`include "hmc_env.sv"
	
endpackage : hmc_pkg
