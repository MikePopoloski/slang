//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Programmable Interrupt Controller                  ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  PIC according to OR1K architectural specification.          ////
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
// $Log: or1200_pic.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_pic(
	// RISC Internal Interface
	clk, rst, spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o,
	pic_wakeup, intr,
	
	// PIC Interface
	pic_int
);

//
// RISC Internal Interface
//
input		clk;		// Clock
input		rst;		// Reset
input		spr_cs;		// SPR CS
input		spr_write;	// SPR Write
input	[31:0]	spr_addr;	// SPR Address
input	[31:0]	spr_dat_i;	// SPR Write Data
output	[31:0]	spr_dat_o;	// SPR Read Data
output		pic_wakeup;	// Wakeup to the PM
output		intr;		// interrupt
				// exception request

//
// PIC Interface
//
input	[`OR1200_PIC_INTS-1:0]	pic_int;// Interrupt inputs

`ifdef OR1200_PIC_IMPLEMENTED

//
// PIC Mask Register bits (or no register)
//
`ifdef OR1200_PIC_PICMR
reg	[`OR1200_PIC_INTS-1:2]	picmr;	// PICMR bits
`else
wire	[`OR1200_PIC_INTS-1:2]	picmr;	// No PICMR register
`endif

//
// PIC Status Register bits (or no register)
//
`ifdef OR1200_PIC_PICSR
reg	[`OR1200_PIC_INTS-1:0]	picsr;	// PICSR bits
`else
wire	[`OR1200_PIC_INTS-1:0]	picsr;	// No PICSR register
`endif

//
// Internal wires & regs
//
wire		picmr_sel;	// PICMR select
wire		picsr_sel;	// PICSR select
wire	[`OR1200_PIC_INTS-1:0] um_ints;// Unmasked interrupts
reg	[31:0] 	spr_dat_o;	// SPR data out

//
// PIC registers address decoder
//
assign picmr_sel = (spr_cs && (spr_addr[`OR1200_PICOFS_BITS] == `OR1200_PIC_OFS_PICMR)) ? 1'b1 : 1'b0;
assign picsr_sel = (spr_cs && (spr_addr[`OR1200_PICOFS_BITS] == `OR1200_PIC_OFS_PICSR)) ? 1'b1 : 1'b0;

//
// Write to PICMR
//
`ifdef OR1200_PIC_PICMR
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		picmr <= {1'b1, {`OR1200_PIC_INTS-3{1'b0}}};
	else if (picmr_sel && spr_write) begin
		picmr <=  spr_dat_i[`OR1200_PIC_INTS-1:2];
	end
`else
assign picmr = (`OR1200_PIC_INTS)'b1;
`endif

//
// Write to PICSR, both CPU and external ints
//
`ifdef OR1200_PIC_PICSR
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		picsr <= {`OR1200_PIC_INTS{1'b0}};
	else if (picsr_sel && spr_write) begin
		picsr <=  spr_dat_i[`OR1200_PIC_INTS-1:0] | um_ints;
	end else
		picsr <=  picsr | um_ints;
`else
assign picsr = pic_int;
`endif

//
// Read PIC registers
//
always @(spr_addr or picmr or picsr)
	case (spr_addr[`OR1200_PICOFS_BITS])	// synopsys parallel_case
`ifdef OR1200_PIC_READREGS
		`OR1200_PIC_OFS_PICMR: begin
		   spr_dat_o[`OR1200_PIC_INTS-1:0] = {picmr, 2'b11};
 `ifdef OR1200_PIC_UNUSED_ZERO
		   spr_dat_o[31:`OR1200_PIC_INTS] = {32-`OR1200_PIC_INTS{1'b0}};
 `endif
		end
`endif
	  default: begin
	     spr_dat_o[`OR1200_PIC_INTS-1:0] = picsr;
`ifdef OR1200_PIC_UNUSED_ZERO
	     spr_dat_o[31:`OR1200_PIC_INTS] = {32-`OR1200_PIC_INTS{1'b0}};
`endif
	  end
	endcase
   
//
// Unmasked interrupts
//
assign um_ints = pic_int & {picmr, 2'b11};

//
// Generate intr
//
assign intr = |um_ints;

//
// Assert pic_wakeup when intr is asserted
//
assign pic_wakeup = intr;

`else

//
// When PIC is not implemented, drive all outputs as would when PIC is disabled
//
assign intr = pic_int[1] | pic_int[0];
assign pic_wakeup= intr;

//
// Read PIC registers
//
`ifdef OR1200_PIC_READREGS
assign spr_dat_o[`OR1200_PIC_INTS-1:0] = `OR1200_PIC_INTS'b0;
`ifdef OR1200_PIC_UNUSED_ZERO
assign spr_dat_o[31:`OR1200_PIC_INTS] = 32-`OR1200_PIC_INTS'b0;
`endif
`endif

`endif

endmodule
