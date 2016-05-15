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
// HMC controller status
//
class reg_openhmc_rf_status_general_c extends cag_rgm_register;

   typedef struct packed {
       bit [15:0] lane_polarity_reversed_;
       bit [5:0] Reserved_0;
       bit [9:0] rx_tokens_remaining_;
       bit [5:0] Reserved_1;
       bit [9:0] hmc_tokens_remaining_;
       bit [5:0] Reserved_2;
       bit [0:0] phy_rx_ready_;
       bit [0:0] phy_tx_ready_;
       bit [2:0] Reserved_3;
       bit [0:0] lanes_reversed_;
       bit [0:0] FERR_N_;
       bit [0:0] sleep_mode_;
       bit [0:0] link_training_;
       bit [0:0] link_up_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_status_general_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_status_general_c");
       super.new(name);
       this.name = name;
       set_address('h0);
   endfunction : new

endclass : reg_openhmc_rf_status_general_c

//
// HMC controller initialization status
//
class reg_openhmc_rf_status_init_c extends cag_rgm_register;

   typedef struct packed {
       bit [1:0] tx_init_state_;
       bit [2:0] rx_init_state_;
       bit [0:0] all_descramblers_aligned_;
       bit [15:0] descrambler_aligned_;
       bit [15:0] descrambler_part_aligned_;
       bit [15:0] lane_descramblers_locked_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_status_init_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_status_init_c");
       super.new(name);
       this.name = name;
       set_address('h8);
   endfunction : new

endclass : reg_openhmc_rf_status_init_c

//
// HMC controller control
//
class reg_openhmc_rf_control_c extends cag_rgm_register;

   typedef struct packed {
       bit [5:0] bit_slip_time_;
       bit [2:0] Reserved_4;
       bit [4:0] irtry_to_send_;
       bit [2:0] Reserved_5;
       bit [4:0] irtry_received_threshold_;
       bit [5:0] Reserved_6;
       bit [9:0] rx_token_count_;
       bit [4:0] Reserved_7;
       bit [0:0] debug_halt_on_tx_retry_;
       bit [0:0] debug_halt_on_error_abort_;
       bit [0:0] debug_dont_send_tret_;
       bit [1:0] Reserved_8;
       bit [0:0] run_length_enable_;
       bit [0:0] scrambler_disable_;
       bit [0:0] warm_reset_;
       bit [0:0] set_hmc_sleep_;
       bit [0:0] hmc_init_cont_set_;
       bit [0:0] p_rst_n_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_control_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_control_c");
       super.new(name);
       this.name = name;
       set_address('h10);
   endfunction : new

endclass : reg_openhmc_rf_control_c

//
// Posted requests sent to the HMC
//
class reg_openhmc_rf_sent_p_c extends cag_rgm_register;

   typedef struct packed {
       bit [63:0] cnt_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_sent_p_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_sent_p_c");
       super.new(name);
       this.name = name;
       set_address('h18);
   endfunction : new

endclass : reg_openhmc_rf_sent_p_c

//
// Nonposted requests sent to the HMC
//
class reg_openhmc_rf_sent_np_c extends cag_rgm_register;

   typedef struct packed {
       bit [63:0] cnt_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_sent_np_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_sent_np_c");
       super.new(name);
       this.name = name;
       set_address('h20);
   endfunction : new

endclass : reg_openhmc_rf_sent_np_c

//
// Read requests sent to the HMC
//
class reg_openhmc_rf_sent_r_c extends cag_rgm_register;

   typedef struct packed {
       bit [63:0] cnt_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_sent_r_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_sent_r_c");
       super.new(name);
       this.name = name;
       set_address('h28);
   endfunction : new

endclass : reg_openhmc_rf_sent_r_c

//
// Count of packets that had data errors but valid flow information
//
class reg_openhmc_rf_poisoned_packets_c extends cag_rgm_register;

   typedef struct packed {
       bit [63:0] cnt_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_poisoned_packets_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_poisoned_packets_c");
       super.new(name);
       this.name = name;
       set_address('h30);
   endfunction : new

endclass : reg_openhmc_rf_poisoned_packets_c

//
// Responses received from the HMC
//
class reg_openhmc_rf_rcvd_rsp_c extends cag_rgm_register;

   typedef struct packed {
       bit [63:0] cnt_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_rcvd_rsp_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_rcvd_rsp_c");
       super.new(name);
       this.name = name;
       set_address('h38);
   endfunction : new

endclass : reg_openhmc_rf_rcvd_rsp_c

//
// Reset performance counters
//
class reg_openhmc_rf_counter_reset_c extends cag_rgm_register;

   typedef struct packed {
       bit rreinit_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_counter_reset_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_counter_reset_c");
       super.new(name);
       this.name = name;
       set_address('h40);
   endfunction : new

endclass : reg_openhmc_rf_counter_reset_c

//
// Count of re-transmit requests
//
class reg_openhmc_rf_tx_link_retries_c extends cag_rgm_register;

   typedef struct packed {
       bit [47:0] count_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_tx_link_retries_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_tx_link_retries_c");
       super.new(name);
       this.name = name;
       set_address('h48);
   endfunction : new

endclass : reg_openhmc_rf_tx_link_retries_c

//
// Count of errors seen on RX
//
class reg_openhmc_rf_errors_on_rx_c extends cag_rgm_register;

   typedef struct packed {
       bit [47:0] count_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_errors_on_rx_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_errors_on_rx_c");
       super.new(name);
       this.name = name;
       set_address('h50);
   endfunction : new

endclass : reg_openhmc_rf_errors_on_rx_c

//
// The number of bit_flips forced by the run length limiter
//
class reg_openhmc_rf_run_length_bit_flip_c extends cag_rgm_register;

   typedef struct packed {
       bit [47:0] count_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_run_length_bit_flip_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_run_length_bit_flip_c");
       super.new(name);
       this.name = name;
       set_address('h58);
   endfunction : new

endclass : reg_openhmc_rf_run_length_bit_flip_c

//
// Indicates the number of error abort modes not cleared in time
//
class reg_openhmc_rf_error_abort_not_cleared_c extends cag_rgm_register;

   typedef struct packed {
       bit [47:0] count_;
   } pkd_flds_s;

   `cag_rgm_register_fields(pkd_flds_s)

   `uvm_object_utils_begin(reg_openhmc_rf_error_abort_not_cleared_c)
       `uvm_field_int(fields,UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name="reg_openhmc_rf_error_abort_not_cleared_c");
       super.new(name);
       this.name = name;
       set_address('h60);
   endfunction : new

endclass : reg_openhmc_rf_error_abort_not_cleared_c

class rf_openhmc_rf_c extends cag_rgm_register_file;

   rand reg_openhmc_rf_status_general_c status_general;
   rand reg_openhmc_rf_status_init_c status_init;
   rand reg_openhmc_rf_control_c control;
   rand reg_openhmc_rf_sent_p_c sent_p;
   rand reg_openhmc_rf_sent_np_c sent_np;
   rand reg_openhmc_rf_sent_r_c sent_r;
   rand reg_openhmc_rf_poisoned_packets_c poisoned_packets;
   rand reg_openhmc_rf_rcvd_rsp_c rcvd_rsp;
   rand reg_openhmc_rf_counter_reset_c counter_reset;
   rand reg_openhmc_rf_tx_link_retries_c tx_link_retries;
   rand reg_openhmc_rf_errors_on_rx_c errors_on_rx;
   rand reg_openhmc_rf_run_length_bit_flip_c run_length_bit_flip;
   rand reg_openhmc_rf_error_abort_not_cleared_c error_abort_not_cleared;

   `uvm_object_utils(rf_openhmc_rf_c)

   function new(string name="rf_openhmc_rf_c");
       super.new(name);
       this.name = name;
       status_general = reg_openhmc_rf_status_general_c::type_id::create("status_general");
       status_general.set_address('h0);
       add_register(status_general);
       status_init = reg_openhmc_rf_status_init_c::type_id::create("status_init");
       status_init.set_address('h8);
       add_register(status_init);
       control = reg_openhmc_rf_control_c::type_id::create("control");
       control.set_address('h10);
       add_register(control);
       sent_p = reg_openhmc_rf_sent_p_c::type_id::create("sent_p");
       sent_p.set_address('h18);
       add_register(sent_p);
       sent_np = reg_openhmc_rf_sent_np_c::type_id::create("sent_np");
       sent_np.set_address('h20);
       add_register(sent_np);
       sent_r = reg_openhmc_rf_sent_r_c::type_id::create("sent_r");
       sent_r.set_address('h28);
       add_register(sent_r);
       poisoned_packets = reg_openhmc_rf_poisoned_packets_c::type_id::create("poisoned_packets");
       poisoned_packets.set_address('h30);
       add_register(poisoned_packets);
       rcvd_rsp = reg_openhmc_rf_rcvd_rsp_c::type_id::create("rcvd_rsp");
       rcvd_rsp.set_address('h38);
       add_register(rcvd_rsp);
       counter_reset = reg_openhmc_rf_counter_reset_c::type_id::create("counter_reset");
       counter_reset.set_address('h40);
       add_register(counter_reset);
       tx_link_retries = reg_openhmc_rf_tx_link_retries_c::type_id::create("tx_link_retries");
       tx_link_retries.set_address('h48);
       add_register(tx_link_retries);
       errors_on_rx = reg_openhmc_rf_errors_on_rx_c::type_id::create("errors_on_rx");
       errors_on_rx.set_address('h50);
       add_register(errors_on_rx);
       run_length_bit_flip = reg_openhmc_rf_run_length_bit_flip_c::type_id::create("run_length_bit_flip");
       run_length_bit_flip.set_address('h58);
       add_register(run_length_bit_flip);
       error_abort_not_cleared = reg_openhmc_rf_error_abort_not_cleared_c::type_id::create("error_abort_not_cleared");
       error_abort_not_cleared.set_address('h60);
       add_register(error_abort_not_cleared);
   endfunction : new

endclass : rf_openhmc_rf_c

