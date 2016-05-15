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
 
//-- the base test
`include "hmc_base_test.sv"


//-- sequence lib
`include "seq_lib/hmc_seq_lib.sv"

//-- the init sequence
`include "openhmc_init_seq.sv"

//-- Set the HMC model
`include "hmc_model_init_seq.sv"

//-- check registers after test ends
`include "openhmc_check_seq.sv"

`include "simple_test/simple_test_seq.sv"
`include "simple_test/simple_test.sv"

`include "single_pkt_test/single_pkt_test_seq.sv"
`include "single_pkt_test/single_pkt_test.sv"

`include "sleep_mode_test/sleep_mode_test_seq.sv"
`include "sleep_mode_test/sleep_mode_test.sv"

`include "atomic_pkt_test/atomic_pkt_test.sv"
`include "atomic_pkt_test/atomic_pkt_test_seq.sv"

`include "big_pkt_hdelay_test/big_pkt_hdelay_test.sv"
`include "big_pkt_hdelay_test/big_pkt_hdelay_test_seq.sv"

`include "big_pkt_test/big_pkt_test.sv"
`include "big_pkt_test/big_pkt_test_seq.sv"

`include "small_pkt_test/small_pkt_test.sv"
`include "small_pkt_test/small_pkt_test_seq.sv"

`include "big_pkt_zdelay_test/big_pkt_zdelay_test.sv"
`include "big_pkt_zdelay_test/big_pkt_zdelay_test_seq.sv"

`include "high_delay_pkt_test/high_delay_pkt_test.sv"
`include "high_delay_pkt_test/high_delay_pkt_test_seq.sv"

`include "zero_delay_pkt_test/zero_delay_pkt_test.sv"
`include "zero_delay_pkt_test/zero_delay_pkt_test_seq.sv"

`include "non_posted_pkt_test/non_posted_pkt_test.sv"
`include "non_posted_pkt_test/non_posted_pkt_test_seq.sv"

`include "posted_pkt_test/posted_pkt_test.sv"
`include "posted_pkt_test/posted_pkt_test_seq.sv"

`include "small_pkt_hdelay_test/small_pkt_hdelay_test.sv"
`include "small_pkt_hdelay_test/small_pkt_hdelay_test_seq.sv"

`include "small_pkt_zdelay_test/small_pkt_zdelay_test.sv"
`include "small_pkt_zdelay_test/small_pkt_zdelay_test_seq.sv"

`include "init_test/init_test.sv"
`include "init_test/init_test_seq.sv"

`ifdef HMC_UVC
	`include "error_pkt_test/error_pkt_test.sv"
	`include "error_pkt_test/error_pkt_test_seq.sv"
	`include "bit_error_test/bit_error_test.sv"
	`include "bit_error_test/bit_error_test_seq.sv"
`endif