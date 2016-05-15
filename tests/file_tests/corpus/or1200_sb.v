//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Store Buffer                                       ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Implements store buffer.                                    ////
////                                                              ////
////  To Do:                                                      ////
////   - byte combining                                           ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2002 Authors and OPENCORES.ORG                 ////
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
//
// $Log: or1200_sb.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_sb(
	// RISC clock, reset
	clk, rst,

	// Internal RISC bus (SB)
	sb_en,

	// Internal RISC bus (DC<->SB)
	dcsb_dat_i, dcsb_adr_i, dcsb_cyc_i, dcsb_stb_i, dcsb_we_i, dcsb_sel_i, dcsb_cab_i,
	dcsb_dat_o, dcsb_ack_o, dcsb_err_o,

	// BIU bus
	sbbiu_dat_o, sbbiu_adr_o, sbbiu_cyc_o, sbbiu_stb_o, sbbiu_we_o, sbbiu_sel_o, sbbiu_cab_o,
	sbbiu_dat_i, sbbiu_ack_i, sbbiu_err_i
);

parameter dw = `OR1200_OPERAND_WIDTH;
parameter aw = `OR1200_OPERAND_WIDTH;

//
// RISC clock, reset
//
input			clk;		// RISC clock
input			rst;		// RISC reset

//
// Internal RISC bus (SB)
//
input			sb_en;		// SB enable

//
// Internal RISC bus (DC<->SB)
//
input	[dw-1:0]	dcsb_dat_i;	// input data bus
input	[aw-1:0]	dcsb_adr_i;	// address bus
input			dcsb_cyc_i;	// WB cycle
input			dcsb_stb_i;	// WB strobe
input			dcsb_we_i;	// WB write enable
input			dcsb_cab_i;	// CAB input
input	[3:0]		dcsb_sel_i;	// byte selects
output	[dw-1:0]	dcsb_dat_o;	// output data bus
output			dcsb_ack_o;	// ack output
output			dcsb_err_o;	// err output

//
// BIU bus
//
output	[dw-1:0]	sbbiu_dat_o;	// output data bus
output	[aw-1:0]	sbbiu_adr_o;	// address bus
output			sbbiu_cyc_o;	// WB cycle
output			sbbiu_stb_o;	// WB strobe
output			sbbiu_we_o;	// WB write enable
output			sbbiu_cab_o;	// CAB input
output	[3:0]		sbbiu_sel_o;	// byte selects
input	[dw-1:0]	sbbiu_dat_i;	// input data bus
input			sbbiu_ack_i;	// ack output
input			sbbiu_err_i;	// err output

`ifdef OR1200_SB_IMPLEMENTED

//
// Internal wires and regs
//
wire	[4+dw+aw-1:0]	fifo_dat_i;	// FIFO data in
wire	[4+dw+aw-1:0]	fifo_dat_o;	// FIFO data out
wire			fifo_wr;
wire			fifo_rd;
wire			fifo_full;
wire			fifo_empty;
wire			sel_sb;
reg			sb_en_reg;
reg			outstanding_store;
reg			fifo_wr_ack;

//
// FIFO data in/out
//
assign fifo_dat_i = {dcsb_sel_i, dcsb_dat_i, dcsb_adr_i};
assign {sbbiu_sel_o, sbbiu_dat_o, sbbiu_adr_o} = sel_sb ? fifo_dat_o : {dcsb_sel_i, dcsb_dat_i, dcsb_adr_i};

//
// Control
//
assign fifo_wr = dcsb_cyc_i & dcsb_stb_i & dcsb_we_i & ~fifo_full & ~fifo_wr_ack;
assign fifo_rd = ~outstanding_store;
assign dcsb_dat_o = sbbiu_dat_i;
assign dcsb_ack_o = sel_sb ? fifo_wr_ack : sbbiu_ack_i;
assign dcsb_err_o = sel_sb ? 1'b0 : sbbiu_err_i;	// SB never returns error
assign sbbiu_cyc_o = sel_sb ? outstanding_store : dcsb_cyc_i;
assign sbbiu_stb_o = sel_sb ? outstanding_store : dcsb_stb_i;
assign sbbiu_we_o = sel_sb ? 1'b1 : dcsb_we_i;
assign sbbiu_cab_o = sel_sb ? 1'b0 : dcsb_cab_i;
assign sel_sb = sb_en_reg & (~fifo_empty | (fifo_empty & outstanding_store));

//
// SB enable
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		sb_en_reg <= 1'b0;
	else if (sb_en & ~dcsb_cyc_i)
		sb_en_reg <=  1'b1; // enable SB when there is no dcsb transfer in progress
	else if (~sb_en & (~fifo_empty | (fifo_empty & outstanding_store)))
		sb_en_reg <=  1'b0; // disable SB when there is no pending transfers from SB

//
// Store buffer FIFO instantiation
//
or1200_sb_fifo or1200_sb_fifo (
	.clk_i(clk),
	.rst_i(rst),
	.dat_i(fifo_dat_i),
	.wr_i(fifo_wr),
	.rd_i(fifo_rd),
	.dat_o(fifo_dat_o),
	.full_o(fifo_full),
	.empty_o(fifo_empty)
);

//
// fifo_rd
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		outstanding_store <=  1'b0;
	else if (sbbiu_ack_i)
		outstanding_store <=  1'b0;
	else if (sel_sb | fifo_wr)
		outstanding_store <=  1'b1;

//
// fifo_wr_ack
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		fifo_wr_ack <=  1'b0;
	else if (fifo_wr)
		fifo_wr_ack <=  1'b1;
	else
		fifo_wr_ack <=  1'b0;

`else	// !OR1200_SB_IMPLEMENTED

assign sbbiu_dat_o = dcsb_dat_i;
assign sbbiu_adr_o = dcsb_adr_i;
assign sbbiu_cyc_o = dcsb_cyc_i;
assign sbbiu_stb_o = dcsb_stb_i;
assign sbbiu_we_o = dcsb_we_i;
assign sbbiu_cab_o = dcsb_cab_i;
assign sbbiu_sel_o = dcsb_sel_i;
assign dcsb_dat_o = sbbiu_dat_i;
assign dcsb_ack_o = sbbiu_ack_i;
assign dcsb_err_o = sbbiu_err_i;

`endif

endmodule
