//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Generic Single-Port Synchronous RAM                         ////
////                                                              ////
////  This file is part of memory library available from          ////
////  http://www.opencores.org/cvsweb.shtml/generic_memories/     ////
////                                                              ////
////  Description                                                 ////
////  This block is a wrapper with common single-port             ////
////  synchronous memory interface for different                  ////
////  types of ASIC and FPGA RAMs. Beside universal memory        ////
////  interface it also provides behavioral model of generic      ////
////  single-port synchronous RAM.                                ////
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

module or1200_spram
  (
`ifdef OR1200_BIST
   // RAM BIST
   mbist_si_i, mbist_so_o, mbist_ctrl_i,
`endif
   // Generic synchronous single-port RAM interface
   clk, ce, we, addr, di, doq
   );
   
   //
   // Default address and data buses width
   //
   parameter aw = 10;
   parameter dw = 32;
   
`ifdef OR1200_BIST
   //
   // RAM BIST
   //
   input mbist_si_i;
   input [`OR1200_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;
   output 				  mbist_so_o;
`endif
   
   //
   // Generic synchronous single-port RAM interface
   //
   input 				  clk;	// Clock
   input 				  ce;	// Chip enable input
   input 				  we;	// Write enable input
   //input 				  oe;	// Output enable input
   input [aw-1:0] 			  addr;	// address bus inputs
   input [dw-1:0] 			  di;	// input data bus
   output [dw-1:0] 			  doq;	// output data bus
   
   //
   // Internal wires and registers
   //

   //
   // Generic single-port synchronous RAM model
   //
   
   //
   // Generic RAM's registers and wires
   //
`ifdef OR1200_GENERIC   
   reg [dw-1:0] 			  mem [(1<<aw)-1:0] /*synthesis syn_ramstyle = "no_rw_check"*/;
`else
   reg [dw-1:0] 			  mem [(1<<aw)-1:0];
`endif
   reg [aw-1:0] 			  addr_reg;		// RAM address register
   
   //
   // Data output drivers
   //
   //assign doq = (oe) ? mem[addr_reg] : {dw{1'b0}};
   assign doq = mem[addr_reg];
   
   //
   // RAM read address register
   //
   always @(posedge clk)
     if (ce)
       addr_reg <=  addr;
   
   //
   // RAM write
   //
   always @(posedge clk)
     if (we && ce)
       mem[addr] <=  di;
   
endmodule // or1200_spram
