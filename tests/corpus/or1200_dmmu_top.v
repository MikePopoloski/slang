//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Data MMU top level                                 ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Instantiation of all DMMU blocks.                           ////
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
// $Log: or1200_dmmu_top.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

//
// Data MMU
//

module or1200_dmmu_top(
	// Rst and clk
	clk, rst,

	// CPU i/f
	dc_en, dmmu_en, supv, dcpu_adr_i, dcpu_cycstb_i, dcpu_we_i,
	dcpu_tag_o, dcpu_err_o,

	// SPR access
	spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o,

`ifdef OR1200_BIST
	// RAM BIST
	mbist_si_i, mbist_so_o, mbist_ctrl_i,
`endif

	// DC i/f
	qmemdmmu_err_i, qmemdmmu_tag_i, qmemdmmu_adr_o, qmemdmmu_cycstb_o, qmemdmmu_ci_o
);

parameter dw = `OR1200_OPERAND_WIDTH;
parameter aw = `OR1200_OPERAND_WIDTH;

//
// I/O
//

//
// Clock and reset
//
input				clk;
input				rst;

//
// CPU I/F
//
input				dc_en;
input				dmmu_en;
input				supv;
input	[aw-1:0]		dcpu_adr_i;
input				dcpu_cycstb_i;
input				dcpu_we_i;
output	[3:0]			dcpu_tag_o;
output				dcpu_err_o;

//
// SPR access
//
input				spr_cs;
input				spr_write;
input	[aw-1:0]		spr_addr;
input	[31:0]			spr_dat_i;
output	[31:0]			spr_dat_o;

`ifdef OR1200_BIST
//
// RAM BIST
//
input mbist_si_i;
input [`OR1200_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;
output mbist_so_o;
`endif

//
// DC I/F
//
input				qmemdmmu_err_i;
input	[3:0]			qmemdmmu_tag_i;
output	[aw-1:0]		qmemdmmu_adr_o;
output				qmemdmmu_cycstb_o;
output				qmemdmmu_ci_o;

//
// Internal wires and regs
//
wire				dtlb_spr_access;
wire	[31:`OR1200_DMMU_PS]	dtlb_ppn;
wire				dtlb_hit;
wire				dtlb_uwe;
wire				dtlb_ure;
wire				dtlb_swe;
wire				dtlb_sre;
wire	[31:0]			dtlb_dat_o;
wire				dtlb_en;
wire				dtlb_ci;
wire				fault;
wire				miss;
`ifdef OR1200_NO_DMMU
`else
reg				dtlb_done;
reg	[31:`OR1200_DMMU_PS]	dcpu_vpn_r;
`endif

//
// Implemented bits inside match and translate registers
//
// dtlbwYmrX: vpn 31-10  v 0
// dtlbwYtrX: ppn 31-10  swe 9  sre 8  uwe 7  ure 6
//
// dtlb memory width:
// 19 bits for ppn
// 13 bits for vpn
// 1 bit for valid
// 4 bits for protection
// 1 bit for cache inhibit

`ifdef OR1200_NO_DMMU

//
// Put all outputs in inactive state
//
assign spr_dat_o = 32'h00000000;
assign qmemdmmu_adr_o = dcpu_adr_i;
assign dcpu_tag_o = qmemdmmu_tag_i;
assign qmemdmmu_cycstb_o = dcpu_cycstb_i;
assign dcpu_err_o = qmemdmmu_err_i;
assign qmemdmmu_ci_o = `OR1200_DMMU_CI;
`ifdef OR1200_BIST
assign mbist_so_o = mbist_si_i;
`endif

`else

//
// DTLB SPR access
//
// 0A00 - 0AFF  dtlbmr w0
// 0A00 - 0A3F  dtlbmr w0 [63:0]
//
// 0B00 - 0BFF  dtlbtr w0
// 0B00 - 0B3F  dtlbtr w0 [63:0]
//
assign dtlb_spr_access = spr_cs;

//
// Tags:
//
// OR1200_DTAG_TE - TLB miss Exception
// OR1200_DTAG_PE - Page fault Exception
//
assign dcpu_tag_o = miss ? `OR1200_DTAG_TE : fault ? `OR1200_DTAG_PE : qmemdmmu_tag_i;

//
// dcpu_err_o
//
assign dcpu_err_o = miss | fault | qmemdmmu_err_i;

//
// Assert dtlb_done one clock cycle after new address and dtlb_en must be active
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		dtlb_done <=  1'b0;
	else if (dtlb_en)
		dtlb_done <=  dcpu_cycstb_i;
	else
		dtlb_done <=  1'b0;

//
// Cut transfer if something goes wrong with translation. Also delayed signals 
// because of translation delay.
assign qmemdmmu_cycstb_o = (dc_en & dmmu_en) ? 
			   !(miss | fault) & dtlb_done & dcpu_cycstb_i : 
			   !(miss | fault) & dcpu_cycstb_i;


//
// Cache Inhibit
//
assign qmemdmmu_ci_o = dmmu_en ? dtlb_ci : `OR1200_DMMU_CI;

//
// Register dcpu_adr_i's VPN for use when DMMU is not enabled but PPN is 
// expected to come one clock cycle after offset part.
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		dcpu_vpn_r <=  {32-`OR1200_DMMU_PS{1'b0}};
	else
		dcpu_vpn_r <=  dcpu_adr_i[31:`OR1200_DMMU_PS];

//
// Physical address is either translated virtual address or
// simply equal when DMMU is disabled
//
assign qmemdmmu_adr_o = dmmu_en ? {dtlb_ppn, dcpu_adr_i[`OR1200_DMMU_PS-1:0]} :
			          dcpu_adr_i;

//
// Output to SPRS unit
//
assign spr_dat_o = dtlb_spr_access ? dtlb_dat_o : 32'h00000000;

//
// Page fault exception logic
//
assign fault = dtlb_done &
	(  (!dcpu_we_i & !supv & !dtlb_ure) // Load in user mode not enabled
	   || (!dcpu_we_i & supv & !dtlb_sre) // Load in supv mode not enabled
	   || (dcpu_we_i & !supv & !dtlb_uwe) // Store in user mode not enabled
	   || (dcpu_we_i & supv & !dtlb_swe)); // Store in supv mode not enabled

//
// TLB Miss exception logic
//
assign miss = dtlb_done & !dtlb_hit;

//
// DTLB Enable
//
assign dtlb_en = dmmu_en & dcpu_cycstb_i;

//
// Instantiation of DTLB
//
or1200_dmmu_tlb or1200_dmmu_tlb(
	// Rst and clk
        .clk(clk),
	.rst(rst),

        // I/F for translation
        .tlb_en(dtlb_en),
	.vaddr(dcpu_adr_i),
	.hit(dtlb_hit),
	.ppn(dtlb_ppn),
	.uwe(dtlb_uwe),
	.ure(dtlb_ure),
	.swe(dtlb_swe),
	.sre(dtlb_sre),
	.ci(dtlb_ci),

`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(mbist_si_i),
	.mbist_so_o(mbist_so_o),
	.mbist_ctrl_i(mbist_ctrl_i),
`endif

        // SPR access
        .spr_cs(dtlb_spr_access),
	.spr_write(spr_write),
	.spr_addr(spr_addr),
	.spr_dat_i(spr_dat_i),
	.spr_dat_o(dtlb_dat_o)
);

`endif

endmodule
