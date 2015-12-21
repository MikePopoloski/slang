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
////  Supported ASIC RAMs are:                                    ////
////  - Artisan Double-Port Sync RAM                              ////
////  - Avant! Two-Port Sync RAM (*)                              ////
////  - Virage 2-port Sync RAM                                    ////
////                                                              ////
////  Supported FPGA RAMs are:                                    ////
////  - Xilinx Virtex RAMB16                                      ////
////  - Xilinx Virtex RAMB4                                       ////
////  - Altera LPM                                                ////
////                                                              ////
////  To Do:                                                      ////
////   - fix Avant!                                               ////
////   - xilinx rams need external tri-state logic                ////
////   - add additional RAMs                                      ////
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
// $Log: or1200_dpram_32x32.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Coding style changed.
//
// Revision 1.10  2005/10/19 11:37:56  jcastillo
// Added support for RAMB16 Xilinx4/Spartan3 primitives
//
// Revision 1.9  2004/06/08 18:15:48  lampret
// Changed behavior of the simulation generic models
//
// Revision 1.8  2004/04/05 08:29:57  lampret
// Merged branch_qmem into main tree.
//
// Revision 1.7.4.1  2003/07/08 15:36:37  lampret
// Added embedded memory QMEM.
//
// Revision 1.7  2003/04/07 01:19:07  lampret
// Added Altera LPM RAMs. Changed generic RAM output when OE inactive.
//
// Revision 1.6  2002/03/28 19:25:42  lampret
// Added second type of Virtual Silicon two-port SRAM (for register file). Changed defines for VS STP RAMs.
//
// Revision 1.5  2002/02/01 19:56:54  lampret
// Fixed combinational loops.
//
// Revision 1.4  2002/01/23 07:52:36  lampret
// Changed default reset values for SR and ESR to match or1ksim's. Fixed flop model in or1200_dpram_32x32 when OR1200_XILINX_RAM32X1D is defined.
//
// Revision 1.3  2002/01/19 14:10:22  lampret
// Fixed OR1200_XILINX_RAM32X1D.
//
// Revision 1.2  2002/01/15 06:12:22  lampret
// Fixed module name when compiling with OR1200_XILINX_RAM32X1D
//
// Revision 1.1  2002/01/03 08:16:15  lampret
// New prefixes for RTL files, prefixed module names. Updated cache controllers and MMUs.
//
// Revision 1.10  2001/11/05 14:48:00  lampret
// Added missing endif
//
// Revision 1.9  2001/11/02 18:57:14  lampret
// Modified virtual silicon instantiations.
//
// Revision 1.8  2001/10/22 19:39:56  lampret
// Fixed parameters in generic sprams.
//
// Revision 1.7  2001/10/21 17:57:16  lampret
// Removed params from generic_XX.v. Added translate_off/on in sprs.v and id.v. Removed spr_addr from dc.v and ic.v. Fixed CR+LF.
//
// Revision 1.6  2001/10/14 13:12:09  lampret
// MP3 version.
//
// Revision 1.1.1.1  2001/10/06 10:18:36  igorm
// no message
//
// Revision 1.1  2001/08/09 13:39:33  lampret
// Major clean-up.
//
// Revision 1.2  2001/07/30 05:38:02  lampret
// Adding empty directories required by HDL coding guidelines
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_dpram_32x32(
	// Generic synchronous double-port RAM interface
	clk_a, rst_a, ce_a, oe_a, addr_a, do_a,
	clk_b, rst_b, ce_b, we_b, addr_b, di_b
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
input			rst_a;	// Reset
input			ce_a;	// Chip enable input
input			oe_a;	// Output enable input
input 	[aw-1:0]	addr_a;	// address bus inputs
output	[dw-1:0]	do_a;	// output data bus
input			clk_b;	// Clock
input			rst_b;	// Reset
input			ce_b;	// Chip enable input
input			we_b;	// Write enable input
input 	[aw-1:0]	addr_b;	// address bus inputs
input	[dw-1:0]	di_b;	// input data bus

//
// Internal wires and registers
//

`ifdef OR1200_ARTISAN_SDP

//
// Instantiation of ASIC memory:
//
// Artisan Synchronous Double-Port RAM (ra2sh)
//
`ifdef UNUSED
art_hsdp_32x32 #(dw, 1<<aw, aw) artisan_sdp(
`else
art_hsdp_32x32 artisan_sdp(
`endif
	.qa(do_a),
	.clka(clk_a),
	.cena(~ce_a),
	.wena(1'b1),
	.aa(addr_a),
	.da(32'h00000000),
	.oena(~oe_a),
	.qb(),
	.clkb(clk_b),
	.cenb(~ce_b),
	.wenb(~we_b),
	.ab(addr_b),
	.db(di_b),
	.oenb(1'b1)
);

`else

`ifdef OR1200_AVANT_ATP

//
// Instantiation of ASIC memory:
//
// Avant! Asynchronous Two-Port RAM
//
avant_atp avant_atp(
	.web(~we),
	.reb(),
	.oeb(~oe),
	.rcsb(),
	.wcsb(),
	.ra(addr),
	.wa(addr),
	.di(di),
	.doq(doq)
);

`else

`ifdef OR1200_VIRAGE_STP

//
// Instantiation of ASIC memory:
//
// Virage Synchronous 2-port R/W RAM
//
virage_stp virage_stp(
	.QA(do_a),
	.QB(),

	.ADRA(addr_a),
	.DA(32'h00000000),
	.WEA(1'b0),
	.OEA(oe_a),
	.MEA(ce_a),
	.CLKA(clk_a),

	.ADRB(addr_b),
	.DB(di_b),
	.WEB(we_b),
	.OEB(1'b1),
	.MEB(ce_b),
	.CLKB(clk_b)
);

`else

`ifdef OR1200_VIRTUALSILICON_STP_T1

//
// Instantiation of ASIC memory:
//
// Virtual Silicon Two-port R/W SRAM Type 1
//
`ifdef UNUSED
vs_hdtp_64x32 #(1<<aw, aw-1, dw-1) vs_ssp(
`else
vs_hdtp_64x32 vs_ssp(
`endif
	.P1CK(clk_a),
	.P1CEN(~ce_a),
	.P1WEN(1'b1),
	.P1OEN(~oe_a),
	.P1ADR({1'b0, addr_a}),
	.P1DI(32'h0000_0000),
	.P1DOUT(do_a),

	.P2CK(clk_b),
	.P2CEN(~ce_b),
	.P2WEN(~ce_b),
	.P2OEN(1'b1),
	.P2ADR({1'b0, addr_b}),
	.P2DI(di_b),
	.P2DOUT()
);

`else

`ifdef OR1200_VIRTUALSILICON_STP_T2

//
// Instantiation of ASIC memory:
//
// Virtual Silicon Two-port R/W SRAM Type 2
//
`ifdef UNUSED
vs_hdtp_32x32 #(1<<aw, aw-1, dw-1) vs_ssp(
`else
vs_hdtp_32x32 vs_ssp(
`endif
        .RCK(clk_a),
        .REN(~ce_a),
        .OEN(~oe_a),
        .RADR(addr_a),
        .DOUT(do_a),

	.WCK(clk_b),
	.WEN(~ce_b),
	.WADR(addr_b),
	.DI(di_b)
);

`else

`ifdef OR1200_XILINX_RAM32X1D

//
// Instantiation of FPGA memory:
//
// Virtex/Spartan2
//

reg	[4:0]	addr_a_r;

always @(posedge clk_a or `OR1200_RST_EVENT rst_a)
	if (rst_a == `OR1200_RST_VALUE)
		addr_a_r <=  5'b00000;
	else if (ce_a)
		addr_a_r <=  addr_a;

//
// Block 0
//
or1200_xcv_ram32x8d xcv_ram32x8d_0 (
	.DPO(do_a[7:0]),
	.SPO(),
	.A(addr_b),
	.D(di_b[7:0]),
	.DPRA(addr_a_r),
	.WCLK(clk_b),
	.WE(we_b)
);

//
// Block 1
//
or1200_xcv_ram32x8d xcv_ram32x8d_1 (
	.DPO(do_a[15:8]),
	.SPO(),
	.A(addr_b),
	.D(di_b[15:8]),
	.DPRA(addr_a_r),
	.WCLK(clk_b),
	.WE(we_b)
);


//
// Block 2
//
or1200_xcv_ram32x8d xcv_ram32x8d_2 (
	.DPO(do_a[23:16]),
	.SPO(),
	.A(addr_b),
	.D(di_b[23:16]),
	.DPRA(addr_a_r),
	.WCLK(clk_b),
	.WE(we_b)
);

//
// Block 3
//
or1200_xcv_ram32x8d xcv_ram32x8d_3 (
	.DPO(do_a[31:24]),
	.SPO(),
	.A(addr_b),
	.D(di_b[31:24]),
	.DPRA(addr_a_r),
	.WCLK(clk_b),
	.WE(we_b)
);

`else

`ifdef OR1200_XILINX_RAMB4

//
// Instantiation of FPGA memory:
//
// Virtex/Spartan2
//

//
// Block 0
//
RAMB4_S16_S16 ramb4_s16_0(
	.CLKA(clk_a),
	.RSTA(1'b0),
	.ADDRA({3'b000, addr_a}),
	.DIA(16'h0000),
	.ENA(ce_a),
	.WEA(1'b0),
	.DOA(do_a[15:0]),

	.CLKB(clk_b),
	.RSTB(1'b0),
	.ADDRB({3'b000, addr_b}),
	.DIB(di_b[15:0]),
	.ENB(ce_b),
	.WEB(we_b),
	.DOB()
);

//
// Block 1
//
RAMB4_S16_S16 ramb4_s16_1(
	.CLKA(clk_a),
	.RSTA(1'b0),
	.ADDRA({3'b000, addr_a}),
	.DIA(16'h0000),
	.ENA(ce_a),
	.WEA(1'b0),
	.DOA(do_a[31:16]),

	.CLKB(clk_b),
	.RSTB(1'b0),
	.ADDRB({3'b000, addr_b}),
	.DIB(di_b[31:16]),
	.ENB(ce_b),
	.WEB(we_b),
	.DOB()
);

`else

`ifdef OR1200_XILINX_RAMB16

//
// Instantiation of FPGA memory:
//
// Virtex4/Spartan3E
//
// Added By Nir Mor
//

RAMB16_S36_S36 ramb16_s36_s36(
	.CLKA(clk_a),
	.SSRA(1'b0),
	.ADDRA({4'b0000, addr_a}),
	.DIA(32'h00000000),
	.DIPA(4'h0),
	.ENA(ce_a),
	.WEA(1'b0),
	.DOA(do_a),
	.DOPA(),

	.CLKB(clk_b),
	.SSRB(1'b0),
	.ADDRB({4'b0000, addr_b}),
	.DIB(di_b),
	.DIPB(4'h0),
	.ENB(ce_b),
	.WEB(we_b),
	.DOB(),
	.DOPB()
);

`else

`ifdef OR1200_ALTERA_LPM_XXX

//
// Instantiation of FPGA memory:
//
// Altera LPM
//
// Added By Jamil Khatib
//
altqpram altqpram_component (
        .wraddress_a (addr_a),
        .inclocken_a (ce_a),
        .wraddress_b (addr_b),
        .wren_a (we_a),
        .inclocken_b (ce_b),
        .wren_b (we_b),
        .inaclr_a (1'b0),
        .inaclr_b (1'b0),
        .inclock_a (clk_a),
        .inclock_b (clk_b),
        .data_a (di_a),
        .data_b (di_b),
        .q_a (do_a),
        .q_b (do_b)
);

defparam altqpram_component.operation_mode = "BIDIR_DUAL_PORT",
        altqpram_component.width_write_a = dw,
        altqpram_component.widthad_write_a = aw,
        altqpram_component.numwords_write_a = dw,
        altqpram_component.width_read_a = dw,
        altqpram_component.widthad_read_a = aw,
        altqpram_component.numwords_read_a = dw,
        altqpram_component.width_write_b = dw,
        altqpram_component.widthad_write_b = aw,
        altqpram_component.numwords_write_b = dw,
        altqpram_component.width_read_b = dw,
        altqpram_component.widthad_read_b = aw,
        altqpram_component.numwords_read_b = dw,
        altqpram_component.indata_reg_a = "INCLOCK_A",
        altqpram_component.wrcontrol_wraddress_reg_a = "INCLOCK_A",
        altqpram_component.outdata_reg_a = "INCLOCK_A",
        altqpram_component.indata_reg_b = "INCLOCK_B",
        altqpram_component.wrcontrol_wraddress_reg_b = "INCLOCK_B",
        altqpram_component.outdata_reg_b = "INCLOCK_B",
        altqpram_component.indata_aclr_a = "INACLR_A",
        altqpram_component.wraddress_aclr_a = "INACLR_A",
        altqpram_component.wrcontrol_aclr_a = "INACLR_A",
        altqpram_component.outdata_aclr_a = "INACLR_A",
        altqpram_component.indata_aclr_b = "NONE",
        altqpram_component.wraddress_aclr_b = "NONE",
        altqpram_component.wrcontrol_aclr_b = "NONE",
        altqpram_component.outdata_aclr_b = "INACLR_B",
        altqpram_component.lpm_hint = "USE_ESB=ON";
        //examplar attribute altqpram_component NOOPT TRUE

`else

//
// Generic double-port synchronous RAM model
//

//
// Generic RAM's registers and wires
//
reg	[dw-1:0]	mem [(1<<aw)-1:0];	// RAM content
reg	[aw-1:0]	addr_a_reg;		// RAM address registered

//
// Data output drivers
//
assign do_a = (oe_a) ? mem[addr_a_reg] : {dw{1'b0}};

//
// RAM read
//
always @(posedge clk_a or `OR1200_RST_EVENT rst_a)
	if (rst_a == `OR1200_RST_VALUE)
		addr_a_reg <=  {aw{1'b0}};
	else if (ce_a)
		addr_a_reg <=  addr_a;

//
// RAM write
//
always @(posedge clk_b)
	if (ce_b && we_b)
		mem[addr_b] <=  di_b;

`endif	// !OR1200_ALTERA_LPM
`endif	// !OR1200_XILINX_RAMB16
`endif	// !OR1200_XILINX_RAMB4
`endif	// !OR1200_XILINX_RAM32X1D
`endif	// !OR1200_VIRTUALSILICON_SSP_T1
`endif	// !OR1200_VIRTUALSILICON_SSP_T2
`endif	// !OR1200_VIRAGE_STP
`endif	// !OR1200_AVANT_ATP
`endif	// !OR1200_ARTISAN_SDP

endmodule
