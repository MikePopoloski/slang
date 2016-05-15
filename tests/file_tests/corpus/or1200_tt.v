//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Tick Timer                                         ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  TT according to OR1K architectural specification.           ////
////                                                              ////
////  To Do:                                                      ////
////   None                                                       ////
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

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_tt(
	// RISC Internal Interface
	clk, rst, du_stall,
	spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o,
	intr
);

//
// RISC Internal Interface
//
input		clk;		// Clock
input		rst;		// Reset
input		du_stall;	// DU stall
input		spr_cs;		// SPR CS
input		spr_write;	// SPR Write
input	[31:0]	spr_addr;	// SPR Address
input	[31:0]	spr_dat_i;	// SPR Write Data
output	[31:0]	spr_dat_o;	// SPR Read Data
output		intr;		// Interrupt output

`ifdef OR1200_TT_IMPLEMENTED

//
// TT Mode Register bits (or no register)
//
`ifdef OR1200_TT_TTMR
reg	[31:0]	ttmr;	// TTMR bits
`else
wire	[31:0]	ttmr;	// No TTMR register
`endif

//
// TT Count Register bits (or no register)
//
`ifdef OR1200_TT_TTCR
reg	[31:0]	ttcr;	// TTCR bits
`else
wire	[31:0]	ttcr;	// No TTCR register
`endif

//
// Internal wires & regs
//
wire		ttmr_sel;	// TTMR select
wire		ttcr_sel;	// TTCR select
wire		match;		// Asserted when TTMR[TP]
				// is equal to TTCR[27:0]
wire		restart;	// Restart counter when asserted
wire		stop;		// Stop counter when asserted
reg	[31:0] 	spr_dat_o;	// SPR data out

//
// TT registers address decoder
//
assign ttmr_sel = (spr_cs && (spr_addr[`OR1200_TTOFS_BITS] == `OR1200_TT_OFS_TTMR)) ? 1'b1 : 1'b0;
assign ttcr_sel = (spr_cs && (spr_addr[`OR1200_TTOFS_BITS] == `OR1200_TT_OFS_TTCR)) ? 1'b1 : 1'b0;

//
// Write to TTMR or update of TTMR[IP] bit
//
`ifdef OR1200_TT_TTMR
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		ttmr <= 32'b0;
	else if (ttmr_sel && spr_write)
		ttmr <=  spr_dat_i;
	else if (ttmr[`OR1200_TT_TTMR_IE])
		ttmr[`OR1200_TT_TTMR_IP] <=  ttmr[`OR1200_TT_TTMR_IP] | (match & ttmr[`OR1200_TT_TTMR_IE]);
`else
assign ttmr = {2'b11, 30'b0};	// TTMR[M] = 0x3
`endif

//
// Write to or increment of TTCR
//
`ifdef OR1200_TT_TTCR
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		ttcr <= 32'b0;
	else if (restart)
		ttcr <=  32'b0;
	else if (ttcr_sel && spr_write)
		ttcr <=  spr_dat_i;
	else if (!stop)
		ttcr <=  ttcr + 32'd1;
`else
assign ttcr = 32'b0;
`endif

//
// Read TT registers
//
always @(spr_addr or ttmr or ttcr)
	case (spr_addr[`OR1200_TTOFS_BITS])	// synopsys parallel_case
`ifdef OR1200_TT_READREGS
		`OR1200_TT_OFS_TTMR: spr_dat_o = ttmr;
`endif
		default: spr_dat_o = ttcr;
	endcase

//
// A match when TTMR[TP] is equal to TTCR[27:0]
//
assign match = (ttmr[`OR1200_TT_TTMR_TP] == ttcr[27:0]) ? 1'b1 : 1'b0;

//
// Restart when match and TTMR[M]==0x1
//
assign restart = match && (ttmr[`OR1200_TT_TTMR_M] == 2'b01);

//
// Stop when match and TTMR[M]==0x2 or when TTMR[M]==0x0 or when RISC is stalled by debug unit
//
assign stop = match & (ttmr[`OR1200_TT_TTMR_M] == 2'b10) | (ttmr[`OR1200_TT_TTMR_M] == 2'b00) | du_stall;

//
// Generate an interrupt request
//
assign intr = ttmr[`OR1200_TT_TTMR_IP];

`else

//
// When TT is not implemented, drive all outputs as would when TT is disabled
//
assign intr = 1'b0;

//
// Read TT registers
//
`ifdef OR1200_TT_READREGS
assign spr_dat_o = 32'b0;
`endif

`endif

endmodule
