//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's mem2reg alignment                                  ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  Two versions of Memory to register data alignment.          ////
////                                                              ////
////  To Do:                                                      ////
////   - make it smaller and faster                               ////
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
// $Log: or1200_mem2reg.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 
//
// Revision 1.5  2002/09/03 22:28:21  lampret
// As per Taylor Su suggestion all case blocks are full case by default and optionally (OR1200_CASE_DEFAULT) can be disabled to increase clock frequncy.
//
// Revision 1.4  2002/03/29 15:16:56  lampret
// Some of the warnings fixed.
//
// Revision 1.3  2002/03/28 19:14:10  lampret
// Changed define name from OR1200_MEM2REG_FAST to OR1200_IMPL_MEM2REG2
//
// Revision 1.2  2002/01/14 06:18:22  lampret
// Fixed mem2reg bug in FAST implementation. Updated debug unit to work with new genpc/if.
//
// Revision 1.1  2002/01/03 08:16:15  lampret
// New prefixes for RTL files, prefixed module names. Updated cache controllers and MMUs.
//
// Revision 1.9  2001/10/21 17:57:16  lampret
// Removed params from generic_XX.v. Added translate_off/on in sprs.v and id.v. Removed spr_addr from dc.v and ic.v. Fixed CR+LF.
//
// Revision 1.8  2001/10/19 23:28:46  lampret
// Fixed some synthesis warnings. Configured with caches and MMUs.
//
// Revision 1.7  2001/10/14 13:12:09  lampret
// MP3 version.
//
// Revision 1.1.1.1  2001/10/06 10:18:36  igorm
// no message
//
// Revision 1.2  2001/08/09 13:39:33  lampret
// Major clean-up.
//
// Revision 1.1  2001/07/20 00:46:03  lampret
// Development version of RTL. Libraries are missing.
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_mem2reg(addr, lsu_op, memdata, regdata);

parameter width = `OR1200_OPERAND_WIDTH;

//
// I/O
//
input	[1:0]			addr;
input	[`OR1200_LSUOP_WIDTH-1:0]	lsu_op;
input	[width-1:0]		memdata;
output	[width-1:0]		regdata;


//
// In the past faster implementation of mem2reg (today probably slower)
//
`ifdef OR1200_IMPL_MEM2REG2

`define OR1200_M2R_BYTE0 4'b0000
`define OR1200_M2R_BYTE1 4'b0001
`define OR1200_M2R_BYTE2 4'b0010
`define OR1200_M2R_BYTE3 4'b0011
`define OR1200_M2R_EXTB0 4'b0100
`define OR1200_M2R_EXTB1 4'b0101
`define OR1200_M2R_EXTB2 4'b0110
`define OR1200_M2R_EXTB3 4'b0111
`define OR1200_M2R_ZERO  4'b0000

reg	[7:0]			regdata_hh;
reg	[7:0]			regdata_hl;
reg	[7:0]			regdata_lh;
reg	[7:0]			regdata_ll;
reg	[width-1:0]		aligned;
reg	[3:0]			sel_byte0, sel_byte1,
				sel_byte2, sel_byte3;

assign regdata = {regdata_hh, regdata_hl, regdata_lh, regdata_ll};

//
// Byte select 0
//
always @(addr or lsu_op) begin
	casex({lsu_op[2:0], addr})	// synopsys parallel_case
		{3'b01x, 2'b00}:			// lbz/lbs 0
			sel_byte0 = `OR1200_M2R_BYTE3;	// take byte 3
		{3'b01x, 2'b01},			// lbz/lbs 1
		{3'b10x, 2'b00}:			// lhz/lhs 0
			sel_byte0 = `OR1200_M2R_BYTE2;	// take byte 2
		{3'b01x, 2'b10}:			// lbz/lbs 2
			sel_byte0 = `OR1200_M2R_BYTE1;	// take byte 1
		default:				// all other cases
			sel_byte0 = `OR1200_M2R_BYTE0;	// take byte 0
	endcase
end

//
// Byte select 1
//
always @(addr or lsu_op) begin
	casex({lsu_op[2:0], addr})	// synopsys parallel_case
		{3'b010, 2'bxx}:			// lbz
			sel_byte1 = `OR1200_M2R_ZERO;	// zero extend
		{3'b011, 2'b00}:			// lbs 0
			sel_byte1 = `OR1200_M2R_EXTB3;	// sign extend from byte 3
		{3'b011, 2'b01}:			// lbs 1
			sel_byte1 = `OR1200_M2R_EXTB2;	// sign extend from byte 2
		{3'b011, 2'b10}:			// lbs 2
			sel_byte1 = `OR1200_M2R_EXTB1;	// sign extend from byte 1
		{3'b011, 2'b11}:			// lbs 3
			sel_byte1 = `OR1200_M2R_EXTB0;	// sign extend from byte 0
		{3'b10x, 2'b00}:			// lhz/lhs 0
			sel_byte1 = `OR1200_M2R_BYTE3;	// take byte 3
		default:				// all other cases
			sel_byte1 = `OR1200_M2R_BYTE1;	// take byte 1
	endcase
end

//
// Byte select 2
//
always @(addr or lsu_op) begin
	casex({lsu_op[2:0], addr})	// synopsys parallel_case
		{3'b010, 2'bxx},			// lbz
		{3'b100, 2'bxx}:			// lhz
			sel_byte2 = `OR1200_M2R_ZERO;	// zero extend
		{3'b011, 2'b00},			// lbs 0
		{3'b101, 2'b00}:			// lhs 0
			sel_byte2 = `OR1200_M2R_EXTB3;	// sign extend from byte 3
		{3'b011, 2'b01}:			// lbs 1
			sel_byte2 = `OR1200_M2R_EXTB2;	// sign extend from byte 2
		{3'b011, 2'b10},			// lbs 2
		{3'b101, 2'b10}:			// lhs 0
			sel_byte2 = `OR1200_M2R_EXTB1;	// sign extend from byte 1
		{3'b011, 2'b11}:			// lbs 3
			sel_byte2 = `OR1200_M2R_EXTB0;	// sign extend from byte 0
		default:				// all other cases
			sel_byte2 = `OR1200_M2R_BYTE2;	// take byte 2
	endcase
end

//
// Byte select 3
//
always @(addr or lsu_op) begin
	casex({lsu_op[2:0], addr}) // synopsys parallel_case
		{3'b010, 2'bxx},			// lbz
		{3'b100, 2'bxx}:			// lhz
			sel_byte3 = `OR1200_M2R_ZERO;	// zero extend
		{3'b011, 2'b00},			// lbs 0
		{3'b101, 2'b00}:			// lhs 0
			sel_byte3 = `OR1200_M2R_EXTB3;	// sign extend from byte 3
		{3'b011, 2'b01}:			// lbs 1
			sel_byte3 = `OR1200_M2R_EXTB2;	// sign extend from byte 2
		{3'b011, 2'b10},			// lbs 2
		{3'b101, 2'b10}:			// lhs 0
			sel_byte3 = `OR1200_M2R_EXTB1;	// sign extend from byte 1
		{3'b011, 2'b11}:			// lbs 3
			sel_byte3 = `OR1200_M2R_EXTB0;	// sign extend from byte 0
		default:				// all other cases
			sel_byte3 = `OR1200_M2R_BYTE3;	// take byte 3
	endcase
end

//
// Byte 0
//
always @(sel_byte0 or memdata) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte0) // synopsys parallel_case infer_mux
`else
	case(sel_byte0) // synopsys full_case parallel_case infer_mux
`endif
`else
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte0) // synopsys parallel_case
`else
	case(sel_byte0) // synopsys full_case parallel_case
`endif
`endif
		`OR1200_M2R_BYTE0: begin
				regdata_ll = memdata[7:0];
			end
		`OR1200_M2R_BYTE1: begin
				regdata_ll = memdata[15:8];
			end
		`OR1200_M2R_BYTE2: begin
				regdata_ll = memdata[23:16];
			end
`ifdef OR1200_CASE_DEFAULT
		default: begin
`else
		`OR1200_M2R_BYTE3: begin
`endif
				regdata_ll = memdata[31:24];
			end
	endcase
end

//
// Byte 1
//
always @(sel_byte1 or memdata) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte1) // synopsys parallel_case infer_mux
`else
	case(sel_byte1) // synopsys full_case parallel_case infer_mux
`endif
`else
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte1) // synopsys parallel_case
`else
	case(sel_byte1) // synopsys full_case parallel_case
`endif
`endif
		`OR1200_M2R_ZERO: begin
				regdata_lh = 8'h00;
			end
		`OR1200_M2R_BYTE1: begin
				regdata_lh = memdata[15:8];
			end
		`OR1200_M2R_BYTE3: begin
				regdata_lh = memdata[31:24];
			end
		`OR1200_M2R_EXTB0: begin
				regdata_lh = {8{memdata[7]}};
			end
		`OR1200_M2R_EXTB1: begin
				regdata_lh = {8{memdata[15]}};
			end
		`OR1200_M2R_EXTB2: begin
				regdata_lh = {8{memdata[23]}};
			end
`ifdef OR1200_CASE_DEFAULT
		default: begin
`else
		`OR1200_M2R_EXTB3: begin
`endif
				regdata_lh = {8{memdata[31]}};
			end
	endcase
end

//
// Byte 2
//
always @(sel_byte2 or memdata) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte2) // synopsys parallel_case infer_mux
`else
	case(sel_byte2) // synopsys full_case parallel_case infer_mux
`endif
`else
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte2) // synopsys parallel_case
`else
	case(sel_byte2) // synopsys full_case parallel_case
`endif
`endif
		`OR1200_M2R_ZERO: begin
				regdata_hl = 8'h00;
			end
		`OR1200_M2R_BYTE2: begin
				regdata_hl = memdata[23:16];
			end
		`OR1200_M2R_EXTB0: begin
				regdata_hl = {8{memdata[7]}};
			end
		`OR1200_M2R_EXTB1: begin
				regdata_hl = {8{memdata[15]}};
			end
		`OR1200_M2R_EXTB2: begin
				regdata_hl = {8{memdata[23]}};
			end
`ifdef OR1200_CASE_DEFAULT
		default: begin
`else
		`OR1200_M2R_EXTB3: begin
`endif
				regdata_hl = {8{memdata[31]}};
			end
	endcase
end

//
// Byte 3
//
always @(sel_byte3 or memdata) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte3) // synopsys parallel_case infer_mux
`else
	case(sel_byte3) // synopsys full_case parallel_case infer_mux
`endif
`else
`ifdef OR1200_CASE_DEFAULT
	case(sel_byte3) // synopsys parallel_case
`else
	case(sel_byte3) // synopsys full_case parallel_case
`endif
`endif
		`OR1200_M2R_ZERO: begin
				regdata_hh = 8'h00;
			end
		`OR1200_M2R_BYTE3: begin
				regdata_hh = memdata[31:24];
			end
		`OR1200_M2R_EXTB0: begin
				regdata_hh = {8{memdata[7]}};
			end
		`OR1200_M2R_EXTB1: begin
				regdata_hh = {8{memdata[15]}};
			end
		`OR1200_M2R_EXTB2: begin
				regdata_hh = {8{memdata[23]}};
			end
`ifdef OR1200_CASE_DEFAULT
		`OR1200_M2R_EXTB3: begin
`else
		`OR1200_M2R_EXTB3: begin
`endif
				regdata_hh = {8{memdata[31]}};
			end
	endcase
end

`else

//
// Straightforward implementation of mem2reg
//

reg	[width-1:0]		regdata;
reg	[width-1:0]		aligned;

//
// Alignment
//
always @(addr or memdata) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
	case(addr) // synopsys parallel_case infer_mux
`else
	case(addr) // synopsys parallel_case
`endif
		2'b00:
			aligned = memdata;
		2'b01:
			aligned = {memdata[23:0], 8'b0};
		2'b10:
			aligned = {memdata[15:0], 16'b0};
		2'b11:
			aligned = {memdata[7:0], 24'b0};
	endcase
end

//
// Bytes
//
always @(lsu_op or aligned) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
	case(lsu_op) // synopsys parallel_case infer_mux
`else
	case(lsu_op) // synopsys parallel_case
`endif
		`OR1200_LSUOP_LBZ: begin
				regdata[7:0] = aligned[31:24];
				regdata[31:8] = 24'b0;
			end
		`OR1200_LSUOP_LBS: begin
				regdata[7:0] = aligned[31:24];
				regdata[31:8] = {24{aligned[31]}};
			end
		`OR1200_LSUOP_LHZ: begin
				regdata[15:0] = aligned[31:16];
				regdata[31:16] = 16'b0;
			end
		`OR1200_LSUOP_LHS: begin
				regdata[15:0] = aligned[31:16];
				regdata[31:16] = {16{aligned[31]}};
			end
		default:
				regdata = aligned;
	endcase
end

`endif

endmodule
