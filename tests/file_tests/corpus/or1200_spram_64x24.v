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
////  Supported ASIC RAMs are:                                    ////
////  - Artisan Single-Port Sync RAM                              ////
////  - Avant! Two-Port Sync RAM (*)                              ////
////  - Virage Single-Port Sync RAM                               ////
////  - Virtual Silicon Single-Port Sync RAM                      ////
////                                                              ////
////  Supported FPGA RAMs are:                                    ////
////  - Xilinx Virtex RAMB16                                      ////
////  - Xilinx Virtex RAMB4                                       ////
////  - Altera LPM                                                ////
////                                                              ////
////  To Do:                                                      ////
////   - xilinx rams need external tri-state logic                ////
////   - fix avant! two-port ram                                  ////
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
// $Log: or1200_spram_64x24.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Coding style changed.
//
// Revision 1.9  2005/10/19 11:37:56  jcastillo
// Added support for RAMB16 Xilinx4/Spartan3 primitives
//
// Revision 1.8  2004/06/08 18:15:32  lampret
// Changed behavior of the simulation generic models
//
// Revision 1.7  2004/04/05 08:29:57  lampret
// Merged branch_qmem into main tree.
//
// Revision 1.3.4.1  2003/12/09 11:46:48  simons
// Mbist nameing changed, Artisan ram instance signal names fixed, some synthesis waning fixed.
//
// Revision 1.3  2003/04/07 01:19:07  lampret
// Added Altera LPM RAMs. Changed generic RAM output when OE inactive.
//
// Revision 1.2  2002/10/17 20:04:41  lampret
// Added BIST scan. Special VS RAMs need to be used to implement BIST.
//
// Revision 1.1  2002/01/03 08:16:15  lampret
// New prefixes for RTL files, prefixed module names. Updated cache controllers and MMUs.
//
// Revision 1.8  2001/11/02 18:57:14  lampret
// Modified virtual silicon instantiations.
//
// Revision 1.7  2001/10/22 19:39:56  lampret
// Fixed parameters in generic sprams.
//
// Revision 1.6  2001/10/21 17:57:16  lampret
// Removed params from generic_XX.v. Added translate_off/on in sprs.v and id.v. Removed spr_addr from dc.v and ic.v. Fixed CR+LF.
//
// Revision 1.5  2001/10/14 13:12:09  lampret
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

module or1200_spram_64x24(
`ifdef OR1200_BIST
	// RAM BIST
	mbist_si_i, mbist_so_o, mbist_ctrl_i,
`endif
	// Generic synchronous single-port RAM interface
	clk, rst, ce, we, oe, addr, di, doq
);

//
// Default address and data buses width
//
parameter aw = 6;
parameter dw = 24;

`ifdef OR1200_BIST
//
// RAM BIST
//
input mbist_si_i;
input [`OR1200_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;
output mbist_so_o;
`endif

//
// Generic synchronous single-port RAM interface
//
input			clk;	// Clock
input			rst;	// Reset
input			ce;	// Chip enable input
input			we;	// Write enable input
input			oe;	// Output enable input
input 	[aw-1:0]	addr;	// address bus inputs
input	[dw-1:0]	di;	// input data bus
output	[dw-1:0]	doq;	// output data bus

//
// Internal wires and registers
//
`ifdef OR1200_XILINX_RAMB4
wire	[7:0]		unconnected;
`else
`ifdef OR1200_XILINX_RAMB16
wire	[7:0]		unconnected;
`endif // !OR1200_XILINX_RAMB16
`endif // !OR1200_XILINX_RAMB4

`ifdef OR1200_ARTISAN_SSP
`else
`ifdef OR1200_VIRTUALSILICON_SSP
`else
`ifdef OR1200_BIST
assign mbist_so_o = mbist_si_i;
`endif
`endif
`endif

`ifdef OR1200_ARTISAN_SSP

//
// Instantiation of ASIC memory:
//
// Artisan Synchronous Single-Port RAM (ra1sh)
//
`ifdef UNUSED
art_hssp_64x24 #(dw, 1<<aw, aw) artisan_ssp(
`else
`ifdef OR1200_BIST
art_hssp_64x24_bist artisan_ssp(
`else
art_hssp_64x24 artisan_ssp(
`endif
`endif
`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(mbist_si_i),
	.mbist_so_o(mbist_so_o),
	.mbist_ctrl_i(mbist_ctrl_i),
`endif
	.CLK(clk),
	.CEN(~ce),
	.WEN(~we),
	.A(addr),
	.D(di),
	.OEN(~oe),
	.Q(doq)
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

`ifdef OR1200_VIRAGE_SSP

//
// Instantiation of ASIC memory:
//
// Virage Synchronous 1-port R/W RAM
//
virage_ssp virage_ssp(
	.clk(clk),
	.adr(addr),
	.d(di),
	.we(we),
	.oe(oe),
	.me(ce),
	.q(doq)
);

`else

`ifdef OR1200_VIRTUALSILICON_SSP

//
// Instantiation of ASIC memory:
//
// Virtual Silicon Single-Port Synchronous SRAM
//
`ifdef UNUSED
vs_hdsp_64x24 #(1<<aw, aw-1, dw-1) vs_ssp(
`else
`ifdef OR1200_BIST
vs_hdsp_64x24_bist vs_ssp(
`else
vs_hdsp_64x24 vs_ssp(
`endif
`endif
`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(mbist_si_i),
	.mbist_so_o(mbist_so_o),
	.mbist_ctrl_i(mbist_ctrl_i),
`endif
	.CK(clk),
	.ADR(addr),
	.DI(di),
	.WEN(~we),
	.CEN(~ce),
	.OEN(~oe),
	.DOUT(doq)
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
RAMB4_S16 ramb4_s16_0(
	.CLK(clk),
	.RST(1'b0),
	.ADDR({2'b00, addr}),
	.DI(di[15:0]),
	.EN(ce),
	.WE(we),
	.DO(doq[15:0])
);

//
// Block 1
//
RAMB4_S16 ramb4_s16_1(
	.CLK(clk),
	.RST(1'b0),
	.ADDR({2'b00, addr}),
	.DI({8'h00, di[23:16]}),
	.EN(ce),
	.WE(we),
	.DO({unconnected, doq[23:16]})
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

RAMB16_S36 ramb16_s36(
	.CLK(clk),
	.SSR(1'b0),
	.ADDR({3'b000, addr}),
	.DI({8'h00,di}),
	.DIP(4'h0),
	.EN(ce),
	.WE(we),
	.DO({unconnected, doq}),
	.DOP()
);

`else

`ifdef OR1200_ALTERA_LPM

//
// Instantiation of FPGA memory:
//
// Altera LPM
//
// Added By Jamil Khatib
//

wire    wr;

assign  wr = ce & we;

initial $display("Using Altera LPM.");

lpm_ram_dq lpm_ram_dq_component (
        .address(addr),
        .inclock(clk),
        .outclock(clk),
        .data(di),
        .we(wr),
        .q(doq)
);

defparam lpm_ram_dq_component.lpm_width = dw,
        lpm_ram_dq_component.lpm_widthad = aw,
        lpm_ram_dq_component.lpm_indata = "REGISTERED",
        lpm_ram_dq_component.lpm_address_control = "REGISTERED",
        lpm_ram_dq_component.lpm_outdata = "UNREGISTERED",
        lpm_ram_dq_component.lpm_hint = "USE_EAB=ON";
        // examplar attribute lpm_ram_dq_component NOOPT TRUE

`else

//
// Generic single-port synchronous RAM model
//

//
// Generic RAM's registers and wires
//
reg	[dw-1:0]	mem [(1<<aw)-1:0];	// RAM content
reg	[aw-1:0]	addr_reg;		// RAM address register

//
// Data output drivers
//
assign doq = (oe) ? mem[addr_reg] : {dw{1'b0}};

//
// RAM address register
//
always @(posedge clk or `OR1200_RST_EVENT rst)
        if (rst == `OR1200_RST_VALUE)
                addr_reg <=  {aw{1'b0}};
        else if (ce)
                addr_reg <=  addr;
                                                                                                                                                                                                     
//
// RAM write
//
always @(posedge clk)
        if (ce && we)
                mem[addr] <=  di;

`endif	// !OR1200_ALTERA_LPM
`endif	// !OR1200_XILINX_RAMB16
`endif	// !OR1200_XILINX_RAMB4
`endif	// !OR1200_VIRTUALSILICON_SSP
`endif	// !OR1200_VIRAGE_SSP
`endif	// !OR1200_AVANT_ATP
`endif	// !OR1200_ARTISAN_SSP

endmodule
