//
//----------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
//   Copyright 2007-2011 Cadence Design Systems, Inc.
//   Copyright 2010-2011 Synopsys, Inc.
//   All Rights Reserved Worldwide
// 
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`ifndef UVM_MACROS_SVH
`define UVM_MACROS_SVH


// Default settings
`define _protected protected   
`define UVM_USE_FPC
`define UVM_USE_P_FORMAT
//`define UVM_USE_FILE_LINE
`define UVM_DA_TO_QUEUE(Q,DA) Q=DA;
`define _local local
`define uvm_delay(TIME) #(TIME);
`define UVM_USE_TYPENAME
//
// Any vendor specific defines go here.
//
`ifdef VCS
`endif


`ifdef MODEL_TECH
`ifndef QUESTA
`define QUESTA
`endif
`endif

`ifdef QUESTA
`define UVM_EXTRA_TYPENAME_ARG
`endif

`ifdef INCA
  `ifndef INCA_PROTECTED_CTOR
    `undef _protected
    `define _protected 
  `endif
  `ifndef INCA_LOCAL_CTOR
    `undef _local
    `define _local 
  `endif
  `ifndef INCA_UVM_USE_P_FORMAT
    `undef  UVM_USE_P_FORMAT
  `endif
//  `ifndef INCA_UVM_USE_FILE_LINE
//    `undef  UVM_USE_FILE_LINE
//  `endif
  `ifndef INCA_UVM_USE_FPC
    `undef UVM_USE_FPC
  `endif
  `define UVM_USE_PROCESS_CONTAINER
  `undef  UVM_DA_TO_QUEUE
  `define UVM_DA_TO_QUEUE(Q,DA)  foreach (DA[idx]) Q.push_back(DA[idx]);
  `ifndef INCA_USE_TYPENAME
    `undef UVM_USE_TYPENAME
  `endif
`endif

//
// Deprecation Control Macros
//
`ifdef UVM_NO_DEPRECATED
  `define UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
`endif


`include "uvm_version_defines.svh"
`include "uvm_message_defines.svh"
`include "uvm_phase_defines.svh"
`include "uvm_object_defines.svh"
`include "uvm_printer_defines.svh"
`include "uvm_tlm_defines.svh"
`include "uvm_sequence_defines.svh"
`include "uvm_callback_defines.svh"
`include "uvm_reg_defines.svh"
`include "uvm_deprecated_defines.svh"

`endif
