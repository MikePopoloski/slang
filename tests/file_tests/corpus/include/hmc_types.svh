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

`ifndef HMC_TYPES_SVH
`define HMC_TYPES_SVH

typedef enum bit [5:0] {
	HMC_FLOW_TYPE				= 6'h00,
	HMC_WRITE_TYPE				= 6'h08,
	HMC_MISC_WRITE_TYPE			= 6'h10,
	HMC_POSTED_WRITE_TYPE		= 6'h18,
	HMC_POSTED_MISC_WRITE_TYPE	= 6'h20,
	HMC_MODE_READ_TYPE			= 6'h28,
	HMC_READ_TYPE				= 6'h30,
	HMC_RESPONSE_TYPE			= 6'h38
} hmc_command_type;

typedef enum bit [5:0] {
	HMC_NULL				= 6'h00,
	HMC_PRET				= 6'h01,
	HMC_TRET				= 6'h02,
	HMC_IRTRY				= 6'h03,
	HMC_WRITE_16			= 6'h08,
	HMC_WRITE_32			= 6'h09,
	HMC_WRITE_48			= 6'h0a,
	HMC_WRITE_64			= 6'h0b,
	HMC_WRITE_80			= 6'h0c,
	HMC_WRITE_96			= 6'h0d,
	HMC_WRITE_112			= 6'h0e,
	HMC_WRITE_128			= 6'h0f,
	//-- misc write
	HMC_MODE_WRITE			= 6'h10,
	HMC_BIT_WRITE			= 6'h11,
	HMC_DUAL_8B_ADDI		= 6'h12,
	HMC_SINGLE_16B_ADDI		= 6'h13,
	
	HMC_POSTED_WRITE_16		= 6'h18,
	HMC_POSTED_WRITE_32		= 6'h19,
	HMC_POSTED_WRITE_48		= 6'h1a,
	HMC_POSTED_WRITE_64		= 6'h1b,
	HMC_POSTED_WRITE_80		= 6'h1c,
	HMC_POSTED_WRITE_96		= 6'h1d,
	HMC_POSTED_WRITE_112	= 6'h1e,
	HMC_POSTED_WRITE_128	= 6'h1f,
	
	HMC_POSTED_BIT_WRIT			= 6'h21,
	HMC_POSTED_DUAL_8B_ADDI		= 6'h22,
	HMC_POSTED_SINGLE_16B_ADDI	= 6'h23,
	
	HMC_MODE_READ			= 6'h28,
	
	HMC_READ_16				= 6'h30,
	HMC_READ_32				= 6'h31,
	HMC_READ_48				= 6'h32,
	HMC_READ_64				= 6'h33,
	HMC_READ_80				= 6'h34,
	HMC_READ_96				= 6'h35,
	HMC_READ_112			= 6'h36,
	HMC_READ_128			= 6'h37,
	HMC_READ_RESPONSE		= 6'h38,
	HMC_WRITE_RESPONSE		= 6'h39,
	HMC_MODE_READ_RESPONSE	= 6'h3A,
	HMC_MODE_WRITE_RESPONSE	= 6'h3B,
	HMC_ERROR_RESPONSE		= 6'h3E
} hmc_command_encoding;

typedef enum {
	RESET,
	POWER_DOWN,
	INIT,
	PRBS,
	NULL_FLITS,
	TS1,
	NULL_FLITS_2,
	INITIAL_TRETS,
	LINK_UP,
	START_RETRY_INIT,
	CLEAR_RETRY,
	SEND_RETRY_PACKETS
} init_state_t;

`endif // HMC_TYPES_SVH

