//
//-----------------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
//   Copyright 2007-2010 Cadence Design Systems, Inc.
//   Copyright 2010 Synopsys, Inc.
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
//-----------------------------------------------------------------------------


`define UVM_SEQ_ITEM_PULL_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  task get_next_item(output REQ req_arg); imp.get_next_item(req_arg); endtask \
  task try_next_item(output REQ req_arg); imp.try_next_item(req_arg); endtask \
  function void item_done(input RSP rsp_arg = null); imp.item_done(rsp_arg); endfunction \
  task wait_for_sequences(); imp.wait_for_sequences(); endtask \
  function bit has_do_available(); return imp.has_do_available(); endfunction \
  function void put_response(input RSP rsp_arg); imp.put_response(rsp_arg); endfunction \
  task get(output REQ req_arg); imp.get(req_arg); endtask \
  task peek(output REQ req_arg); imp.peek(req_arg); endtask \
  task put(input RSP rsp_arg); imp.put(rsp_arg); endtask

//-----------------------------------------------------------------------------
// Title: Sequence Item Pull Ports
//
// This section defines the port, export, and imp port classes for
// communicating sequence items between <uvm_sequencer #(REQ,RSP)> and
// <uvm_driver #(REQ,RSP)>.
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
//
// Class: uvm_seq_item_pull_port #(REQ,RSP)
//
// UVM provides a port, export, and imp connector for use in sequencer-driver
// communication. All have standard port connector constructors, except that
// uvm_seq_item_pull_port's default min_size argument is 0; it can be left
// unconnected.
//
//-----------------------------------------------------------------------------

class uvm_seq_item_pull_port #(type REQ=int, type RSP=REQ)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
  `UVM_SEQ_PORT(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_port")
  `UVM_SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)

  bit print_enabled;
    
endclass


//-----------------------------------------------------------------------------
//
// Class: uvm_seq_item_pull_export #(REQ,RSP)
//
// This export type is used in sequencer-driver communication. It has the
// standard constructor for exports.
//
//-----------------------------------------------------------------------------

class uvm_seq_item_pull_export #(type REQ=int, type RSP=REQ)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
  `UVM_EXPORT_COMMON(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_export")
  `UVM_SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)
endclass


//-----------------------------------------------------------------------------
//
// Class: uvm_seq_item_pull_imp #(REQ,RSP,IMP)
//
// This imp type is used in sequencer-driver communication. It has the
// standard constructor for imp-type ports.
//
//-----------------------------------------------------------------------------

class uvm_seq_item_pull_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
   // Function: new
  `UVM_IMP_COMMON(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_imp",IMP)
  `UVM_SEQ_ITEM_PULL_IMP(m_imp, REQ, RSP, t, t)

endclass
