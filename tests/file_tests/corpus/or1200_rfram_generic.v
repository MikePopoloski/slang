//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's register file generic memory                       ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  Generic (flip-flop based) register file memory              ////
////                                                              ////
////  To Do:                                                      ////
////   - nothing                                                  ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
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
// $Log: or1200_rfram_generic.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Defines added, coding style changed. 
//
// Revision 1.3  2004/06/08 18:16:32  lampret
// GPR0 hardwired to zero.
//
// Revision 1.2  2002/09/03 22:28:21  lampret
// As per Taylor Su suggestion all case blocks are full case by default and optionally (OR1200_CASE_DEFAULT) can be disabled to increase clock frequncy.
//
// Revision 1.1  2002/06/08 16:23:30  lampret
// Generic flip-flop based memory macro for register file.
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_rfram_generic(
	// Clock and reset
	clk, rst,

	// Port A
	ce_a, addr_a, do_a,

	// Port B
	ce_b, addr_b, do_b,

	// Port W
	ce_w, we_w, addr_w, di_w
);

parameter dw = `OR1200_OPERAND_WIDTH;
parameter aw = `OR1200_REGFILE_ADDR_WIDTH;

//
// I/O
//

//
// Clock and reset
//
input				clk;
input				rst;

//
// Port A
//
input				ce_a;
input	[aw-1:0]		addr_a;
output	[dw-1:0]		do_a;

//
// Port B
//
input				ce_b;
input	[aw-1:0]		addr_b;
output	[dw-1:0]		do_b;

//
// Port W
//
input				ce_w;
input				we_w;
input	[aw-1:0]		addr_w;
input	[dw-1:0]		di_w;

//
// Internal wires and regs
//
reg	[aw-1:0]		intaddr_a;
reg	[aw-1:0]		intaddr_b;
`ifdef OR1200_RFRAM_16REG
reg	[16*dw-1:0]		mem;
`else
reg	[32*dw-1:0]		mem;
`endif
reg	[dw-1:0]		do_a;
reg	[dw-1:0]		do_b;

`ifdef verilator
   // Function to access GPRs (for use by Verilator). No need to hide this one
   // from the simulator, since it has an input (as required by IEEE 1364-2001).
   function [31:0] get_gpr;
      // verilator public
      input [aw-1:0] 		gpr_no;

      get_gpr = { mem[gpr_no*32 + 31], mem[gpr_no*32 + 30],
                  mem[gpr_no*32 + 29], mem[gpr_no*32 + 28],
                  mem[gpr_no*32 + 27], mem[gpr_no*32 + 26],
                  mem[gpr_no*32 + 25], mem[gpr_no*32 + 24],
                  mem[gpr_no*32 + 23], mem[gpr_no*32 + 22],
                  mem[gpr_no*32 + 21], mem[gpr_no*32 + 20],
                  mem[gpr_no*32 + 19], mem[gpr_no*32 + 18],
                  mem[gpr_no*32 + 17], mem[gpr_no*32 + 16],
                  mem[gpr_no*32 + 15], mem[gpr_no*32 + 14],
                  mem[gpr_no*32 + 13], mem[gpr_no*32 + 12],
                  mem[gpr_no*32 + 11], mem[gpr_no*32 + 10],
                  mem[gpr_no*32 +  9], mem[gpr_no*32 +  8],
                  mem[gpr_no*32 +  7], mem[gpr_no*32 +  6],
                  mem[gpr_no*32 +  5], mem[gpr_no*32 +  4],
                  mem[gpr_no*32 +  3], mem[gpr_no*32 +  2],
                  mem[gpr_no*32 +  1], mem[gpr_no*32 +  0] };
      
   endfunction // get_gpr

   // Function to access GPRs (for use by Verilator). No need to hide this one
   // from the simulator, since it has an input (as required by IEEE 1364-2001).
   function [31:0] set_gpr;
      // verilator public
      input [aw-1:0] 		gpr_no;
      input [dw-1:0] 		value;

      mem[gpr_no*32 + 31]   = value[31];
      mem[gpr_no*32 + 30] = value[30];
      mem[gpr_no*32 + 29]  = value[29];
      mem[gpr_no*32 + 28] = value[28];
      mem[gpr_no*32 + 27]  = value[27];
      mem[gpr_no*32 + 26] = value[26];
      mem[gpr_no*32 + 25]  = value[25];
      mem[gpr_no*32 + 24] = value[24];
      mem[gpr_no*32 + 23]  = value[23];
      mem[gpr_no*32 + 22] = value[22];
      mem[gpr_no*32 + 21]  = value[21];
      mem[gpr_no*32 + 20] = value[20];
      mem[gpr_no*32 + 19]  = value[19];
      mem[gpr_no*32 + 18] = value[18];
      mem[gpr_no*32 + 17]  = value[17];
      mem[gpr_no*32 + 16] = value[16];
      mem[gpr_no*32 + 15]  = value[15];
      mem[gpr_no*32 + 14] = value[14];
      mem[gpr_no*32 + 13]  = value[13];
      mem[gpr_no*32 + 12] = value[12];
      mem[gpr_no*32 + 11]  = value[11];
      mem[gpr_no*32 + 10] = value[10];
      mem[gpr_no*32 +  9]  = value[ 9];
      mem[gpr_no*32 +  8] = value[ 8];
      mem[gpr_no*32 +  7]  = value[ 7];
      mem[gpr_no*32 +  6] = value[ 6];
      mem[gpr_no*32 +  5]  = value[ 5];
      mem[gpr_no*32 +  4] = value[ 4];
      mem[gpr_no*32 +  3]  = value[ 3];
      mem[gpr_no*32 +  2] = value[ 2];
      mem[gpr_no*32 +  1]  = value[ 1];
      mem[gpr_no*32 +  0] = value[ 0];

      set_gpr = 0;
      
   endfunction // set_gpr
`endif //  `ifdef verilator
   
//
// Write port
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE) begin
		mem <=  {512'h0, 512'h0};
	end
	else if (ce_w & we_w)
		case (addr_w)	// synopsys parallel_case
			5'd01: mem[32*1+31:32*1] <=  di_w;
			5'd02: mem[32*2+31:32*2] <=  di_w;
			5'd03: mem[32*3+31:32*3] <=  di_w;
			5'd04: mem[32*4+31:32*4] <=  di_w;
			5'd05: mem[32*5+31:32*5] <=  di_w;
			5'd06: mem[32*6+31:32*6] <=  di_w;
			5'd07: mem[32*7+31:32*7] <=  di_w;
			5'd08: mem[32*8+31:32*8] <=  di_w;
			5'd09: mem[32*9+31:32*9] <=  di_w;
			5'd10: mem[32*10+31:32*10] <=  di_w;
			5'd11: mem[32*11+31:32*11] <=  di_w;
			5'd12: mem[32*12+31:32*12] <=  di_w;
			5'd13: mem[32*13+31:32*13] <=  di_w;
			5'd14: mem[32*14+31:32*14] <=  di_w;
			5'd15: mem[32*15+31:32*15] <=  di_w;
`ifdef OR1200_RFRAM_16REG
`else
			5'd16: mem[32*16+31:32*16] <=  di_w;
			5'd17: mem[32*17+31:32*17] <=  di_w;
			5'd18: mem[32*18+31:32*18] <=  di_w;
			5'd19: mem[32*19+31:32*19] <=  di_w;
			5'd20: mem[32*20+31:32*20] <=  di_w;
			5'd21: mem[32*21+31:32*21] <=  di_w;
			5'd22: mem[32*22+31:32*22] <=  di_w;
			5'd23: mem[32*23+31:32*23] <=  di_w;
			5'd24: mem[32*24+31:32*24] <=  di_w;
			5'd25: mem[32*25+31:32*25] <=  di_w;
			5'd26: mem[32*26+31:32*26] <=  di_w;
			5'd27: mem[32*27+31:32*27] <=  di_w;
			5'd28: mem[32*28+31:32*28] <=  di_w;
			5'd29: mem[32*29+31:32*29] <=  di_w;
			5'd30: mem[32*30+31:32*30] <=  di_w;
			5'd31: mem[32*31+31:32*31] <=  di_w;
`endif
			default: mem[32*0+31:32*0] <=  32'h0000_0000;
		endcase

//
// Read port A
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE) begin
		intaddr_a <=  5'h00;
	end
	else if (ce_a)
		intaddr_a <=  addr_a;

always @(mem or intaddr_a)
	case (intaddr_a)	// synopsys parallel_case
		5'd01: do_a = mem[32*1+31:32*1];
		5'd02: do_a = mem[32*2+31:32*2];
		5'd03: do_a = mem[32*3+31:32*3];
		5'd04: do_a = mem[32*4+31:32*4];
		5'd05: do_a = mem[32*5+31:32*5];
		5'd06: do_a = mem[32*6+31:32*6];
		5'd07: do_a = mem[32*7+31:32*7];
		5'd08: do_a = mem[32*8+31:32*8];
		5'd09: do_a = mem[32*9+31:32*9];
		5'd10: do_a = mem[32*10+31:32*10];
		5'd11: do_a = mem[32*11+31:32*11];
		5'd12: do_a = mem[32*12+31:32*12];
		5'd13: do_a = mem[32*13+31:32*13];
		5'd14: do_a = mem[32*14+31:32*14];
		5'd15: do_a = mem[32*15+31:32*15];
`ifdef OR1200_RFRAM_16REG
`else
		5'd16: do_a = mem[32*16+31:32*16];
		5'd17: do_a = mem[32*17+31:32*17];
		5'd18: do_a = mem[32*18+31:32*18];
		5'd19: do_a = mem[32*19+31:32*19];
		5'd20: do_a = mem[32*20+31:32*20];
		5'd21: do_a = mem[32*21+31:32*21];
		5'd22: do_a = mem[32*22+31:32*22];
		5'd23: do_a = mem[32*23+31:32*23];
		5'd24: do_a = mem[32*24+31:32*24];
		5'd25: do_a = mem[32*25+31:32*25];
		5'd26: do_a = mem[32*26+31:32*26];
		5'd27: do_a = mem[32*27+31:32*27];
		5'd28: do_a = mem[32*28+31:32*28];
		5'd29: do_a = mem[32*29+31:32*29];
		5'd30: do_a = mem[32*30+31:32*30];
		5'd31: do_a = mem[32*31+31:32*31];
`endif
		default: do_a = 32'h0000_0000;
	endcase

//
// Read port B
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE) begin
		intaddr_b <=  5'h00;
	end
	else if (ce_b)
		intaddr_b <=  addr_b;

always @(mem or intaddr_b)
	case (intaddr_b)	// synopsys parallel_case
		5'd01: do_b = mem[32*1+31:32*1];
		5'd02: do_b = mem[32*2+31:32*2];
		5'd03: do_b = mem[32*3+31:32*3];
		5'd04: do_b = mem[32*4+31:32*4];
		5'd05: do_b = mem[32*5+31:32*5];
		5'd06: do_b = mem[32*6+31:32*6];
		5'd07: do_b = mem[32*7+31:32*7];
		5'd08: do_b = mem[32*8+31:32*8];
		5'd09: do_b = mem[32*9+31:32*9];
		5'd10: do_b = mem[32*10+31:32*10];
		5'd11: do_b = mem[32*11+31:32*11];
		5'd12: do_b = mem[32*12+31:32*12];
		5'd13: do_b = mem[32*13+31:32*13];
		5'd14: do_b = mem[32*14+31:32*14];
		5'd15: do_b = mem[32*15+31:32*15];
`ifdef OR1200_RFRAM_16REG
`else
		5'd16: do_b = mem[32*16+31:32*16];
		5'd17: do_b = mem[32*17+31:32*17];
		5'd18: do_b = mem[32*18+31:32*18];
		5'd19: do_b = mem[32*19+31:32*19];
		5'd20: do_b = mem[32*20+31:32*20];
		5'd21: do_b = mem[32*21+31:32*21];
		5'd22: do_b = mem[32*22+31:32*22];
		5'd23: do_b = mem[32*23+31:32*23];
		5'd24: do_b = mem[32*24+31:32*24];
		5'd25: do_b = mem[32*25+31:32*25];
		5'd26: do_b = mem[32*26+31:32*26];
		5'd27: do_b = mem[32*27+31:32*27];
		5'd28: do_b = mem[32*28+31:32*28];
		5'd29: do_b = mem[32*29+31:32*29];
		5'd30: do_b = mem[32*30+31:32*30];
		5'd31: do_b = mem[32*31+31:32*31];
`endif
		default: do_b = 32'h0000_0000;
	endcase

endmodule
