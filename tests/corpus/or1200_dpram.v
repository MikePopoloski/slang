//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Generic Double-Port Synchronous RAM                         ////
////                                                              ////
////  This file is part of memory library available from          ////
////  http://www.opencores.org/cvsweb.shtml/generic_memories/     ////
////                                                              ////
////  Description                                                 ////
////  This block is a wrapper with common double-port             ////
////  synchronous memory interface for different                  ////
////  types of ASIC and FPGA RAMs. Beside universal memory        ////
////  interface it also provides behavioral model of generic      ////
////  double-port synchronous RAM.                                ////
////  It should be used in all OPENCORES designs that want to be  ////
////  portable accross different target technologies and          ////
////  independent of target memory.                               ////
////                                                              ////
////  Author(s):                                                  ////
////      - Michael Unneback, unneback@opencores.org              ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// CVS Revision History
//
// $Log: or1200_dpram_32x32.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// New 
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_dpram
  (
   // Generic synchronous double-port RAM interface
   clk_a, ce_a, addr_a, do_a,
   clk_b, ce_b, we_b, addr_b, di_b
   );
   
   //
   // Default address and data buses width
   //
   parameter aw = 5;
   parameter dw = 32;
   
   //
   // Generic synchronous double-port RAM interface
   //
   input			clk_a;	// Clock
   input			ce_a;	// Chip enable input
   input [aw-1:0] 		addr_a;	// address bus inputs
   output [dw-1:0] 		do_a;	// output data bus
   input			clk_b;	// Clock
   input			ce_b;	// Chip enable input
   input			we_b;	// Write enable input
   input [aw-1:0] 		addr_b;	// address bus inputs
   input [dw-1:0] 		di_b;	// input data bus
   
   //
   // Internal wires and registers
   //
   
   //
   // Generic double-port synchronous RAM model
   //
   
   //
   // Generic RAM's registers and wires
   //
   reg [dw-1:0] 		mem [(1<<aw)-1:0] /*synthesis syn_ramstyle = "no_rw_check"*/;	// RAM content
   reg [aw-1:0] 		addr_a_reg;		// RAM address registered


   // Function to access GPRs (for use by Verilator). No need to hide this one
   // from the simulator, since it has an input (as required by IEEE 1364-2001).
   function [31:0] get_gpr;
      // verilator public
      input [aw-1:0] 		gpr_no;

      get_gpr = mem[gpr_no];
      
   endfunction // get_gpr

   function [31:0] set_gpr;
      // verilator public
      input [aw-1:0] 		gpr_no;
      input [dw-1:0] 		value;
      begin
	 mem[gpr_no] = value;
	 set_gpr = 0;
      end
   endfunction // get_gpr
   
   //
   // Data output drivers
   //
   //assign do_a = (oe_a) ? mem[addr_a_reg] : {dw{1'b0}};
   assign do_a = mem[addr_a_reg];
   
   
   //
   // RAM read
   //
   always @(posedge clk_a)
     if (ce_a)
       addr_a_reg <=  addr_a;
   
   //
   // RAM write
   //
   always @(posedge clk_b)
     if (ce_b & we_b)
       mem[addr_b] <=  di_b;
   
endmodule // or1200_dpram
