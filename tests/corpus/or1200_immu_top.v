//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Instruction MMU top level                          ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Instantiation of all IMMU blocks.                           ////
////                                                              ////
////  To Do:                                                      ////
////   - cache inhibit                                            ////
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

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

//
// Insn MMU
//

module or1200_immu_top(
	// Rst and clk
	clk, rst,

	// CPU i/f
	ic_en, immu_en, supv, icpu_adr_i, icpu_cycstb_i,
	icpu_adr_o, icpu_tag_o, icpu_rty_o, icpu_err_o,

	// SR Interface
	boot_adr_sel_i,

	// SPR access
	spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o,

`ifdef OR1200_BIST
	// RAM BIST
	mbist_si_i, mbist_so_o, mbist_ctrl_i,
`endif

	// QMEM i/f
	qmemimmu_rty_i, qmemimmu_err_i, qmemimmu_tag_i, qmemimmu_adr_o, qmemimmu_cycstb_o, qmemimmu_ci_o
);

parameter dw = `OR1200_OPERAND_WIDTH;
parameter aw = `OR1200_OPERAND_WIDTH;
parameter boot_adr = `OR1200_BOOT_ADR;

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
input				ic_en;
input				immu_en;
input				supv;
input	[aw-1:0]		icpu_adr_i;
input				icpu_cycstb_i;
output	[aw-1:0]		icpu_adr_o;
output	[3:0]			icpu_tag_o;
output				icpu_rty_o;
output				icpu_err_o;

//
// SR Interface
//
input				boot_adr_sel_i;

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
// IC I/F
//
input				qmemimmu_rty_i;
input				qmemimmu_err_i;
input	[3:0]			qmemimmu_tag_i;
output	[aw-1:0]		qmemimmu_adr_o;
output				qmemimmu_cycstb_o;
output				qmemimmu_ci_o;

//
// Internal wires and regs
//
wire				itlb_spr_access;
wire	[31:`OR1200_IMMU_PS]	itlb_ppn;
wire				itlb_hit;
wire				itlb_uxe;
wire				itlb_sxe;
wire	[31:0]			itlb_dat_o;
wire				itlb_en;
wire				itlb_ci;
wire				itlb_done;
wire				fault;
wire				miss;
wire				page_cross;
reg	[31:0]			icpu_adr_default;
reg				icpu_adr_select;
reg		[31:0]		icpu_adr_o;
reg	[31:`OR1200_IMMU_PS]	icpu_vpn_r;
`ifdef OR1200_NO_IMMU
`else
reg				itlb_en_r;
reg				dis_spr_access_frst_clk;
reg				dis_spr_access_scnd_clk;
`endif

//
// Implemented bits inside match and translate registers
//
// itlbwYmrX: vpn 31-10  v 0
// itlbwYtrX: ppn 31-10  uxe 7  sxe 6
//
// itlb memory width:
// 19 bits for ppn
// 13 bits for vpn
// 1 bit for valid
// 2 bits for protection
// 1 bit for cache inhibit

//
// icpu_adr_o
//
`ifdef OR1200_REGISTERED_OUTPUTS
wire	[31:0]			icpu_adr_boot = boot_adr;

always @(`OR1200_RST_EVENT rst or posedge clk)
	// default value 
	if (rst == `OR1200_RST_VALUE) begin
	        // select async. value due to reset state
		icpu_adr_default <=  32'h0000_0100;
		icpu_adr_select  <=  1'b1;		
	end
	// selected value (different from default) is written 
        // into FF after reset state
	else if (icpu_adr_select) begin
	        // dynamic value can only be assigned to FF out of reset!
		icpu_adr_default <=  icpu_adr_boot;
	        // select FF value 
		icpu_adr_select  <=  1'b0;
	end
	else begin
		icpu_adr_default <=  icpu_adr_i;
	end

// select async. value for boot address after reset - PC jumps to the address 
// selected after boot! 
   //assign icpu_adr_boot = {(boot_adr_sel_i ? `OR1200_EXCEPT_EPH1_P : 
   // `OR1200_EXCEPT_EPH0_P), 12'h100} ;

always @(icpu_adr_boot or icpu_adr_default or icpu_adr_select)
	if (icpu_adr_select)
	        // async. value is selected due to reset state 
		icpu_adr_o = icpu_adr_boot ;
	else
	        // FF value is selected 2nd clock after reset state 
		icpu_adr_o = icpu_adr_default ;		
`else
Unsupported !!!
`endif

//
// Page cross
//
// Asserted when CPU address crosses page boundary. Most of the time it is zero.
//
assign page_cross = icpu_adr_i[31:`OR1200_IMMU_PS] != icpu_vpn_r;

//
// Register icpu_adr_i's VPN for use when IMMU is not enabled but PPN is expected to come
// one clock cycle after offset part.
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		icpu_vpn_r <=  {32-`OR1200_IMMU_PS{1'b0}};
	else
		icpu_vpn_r <=  icpu_adr_i[31:`OR1200_IMMU_PS];

`ifdef OR1200_NO_IMMU

//
// Put all outputs in inactive state
//
assign spr_dat_o = 32'h00000000;
assign qmemimmu_adr_o = icpu_adr_i;
assign icpu_tag_o = qmemimmu_tag_i;
assign qmemimmu_cycstb_o = icpu_cycstb_i & ~page_cross;
assign icpu_rty_o = qmemimmu_rty_i;
assign icpu_err_o = qmemimmu_err_i;
assign qmemimmu_ci_o = `OR1200_IMMU_CI;
`ifdef OR1200_BIST
assign mbist_so_o = mbist_si_i;
`endif
`else

//
// ITLB SPR access
//
// 1200 - 12FF  itlbmr w0
// 1200 - 123F  itlbmr w0 [63:0]
//
// 1300 - 13FF  itlbtr w0
// 1300 - 133F  itlbtr w0 [63:0]
//
assign itlb_spr_access = spr_cs & ~dis_spr_access_scnd_clk;

//
// Disable ITLB SPR access
//
// This flops are used to mask ITLB miss/fault exception
// during first & second clock cycles of accessing ITLB SPR. In
// subsequent clock cycles it is assumed that ITLB SPR
// access was accomplished and that normal instruction fetching
// can proceed.
//
// spr_cs sets dis_spr_access_frst_clk and icpu_rty_o clears it.
// dis_spr_access_frst_clk  sets dis_spr_access_scnd_clk and 
// icpu_rty_o clears it.
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		dis_spr_access_frst_clk  <=  1'b0;
	else if (!icpu_rty_o)
		dis_spr_access_frst_clk  <=  1'b0;
	else if (spr_cs)
		dis_spr_access_frst_clk  <=  1'b1;

always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		dis_spr_access_scnd_clk  <=  1'b0;
	else if (!icpu_rty_o)
		dis_spr_access_scnd_clk  <=  1'b0;
	else if (dis_spr_access_frst_clk)
		dis_spr_access_scnd_clk  <=  1'b1;

//
// Tags:
//
// OR1200_ITAG_TE - TLB miss Exception
// OR1200_ITAG_PE - Page fault Exception
//
assign icpu_tag_o = miss ? `OR1200_ITAG_TE : fault ? `OR1200_ITAG_PE : qmemimmu_tag_i;

//
// icpu_rty_o
//
// assign icpu_rty_o = !icpu_err_o & qmemimmu_rty_i;
//assign icpu_rty_o = qmemimmu_rty_i | itlb_spr_access & immu_en;
assign icpu_rty_o = qmemimmu_rty_i;

//
// icpu_err_o
//
assign icpu_err_o = miss | fault | qmemimmu_err_i;

//
// Assert itlb_en_r after one clock cycle and when there is no
// ITLB SPR access
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		itlb_en_r <=  1'b0;
	else
		itlb_en_r <=  itlb_en & ~itlb_spr_access;

//
// ITLB lookup successful
//
assign itlb_done = itlb_en_r & ~page_cross;

//
// Cut transfer when access (mtspr/mfspr) to/from ITLB occure or if something goes 
// wrong with translation. If IC is disabled, use delayed signals.
//
// assign qmemimmu_cycstb_o = (!ic_en & immu_en) ? ~(miss | fault) & icpu_cycstb_i & ~page_cross : (miss | fault) ? 1'b0 : icpu_cycstb_i & ~page_cross; // DL
//assign qmemimmu_cycstb_o = immu_en ? ~(miss | fault) & icpu_cycstb_i & ~page_cross & itlb_done : icpu_cycstb_i & ~page_cross;
assign qmemimmu_cycstb_o = immu_en ? ~(miss | fault) & icpu_cycstb_i & ~page_cross & itlb_done & ~itlb_spr_access : icpu_cycstb_i & ~page_cross;

//
// Cache Inhibit
//
// Cache inhibit is not really needed for instruction memory subsystem.
// If we would doq it, we would doq it like this.
// assign qmemimmu_ci_o = immu_en ? itlb_done & itlb_ci : `OR1200_IMMU_CI;
// However this causes an async combinatorial loop so we stick to
// no cache inhibit.
//assign qmemimmu_ci_o = `OR1200_IMMU_CI;
// Cache inhibit without an async combinatorial loop 
assign qmemimmu_ci_o = immu_en ? itlb_ci : `OR1200_IMMU_CI;


//
// Physical address is either translated virtual address or
// simply equal when IMMU is disabled
//
//assign qmemimmu_adr_o = itlb_done ? {itlb_ppn, icpu_adr_i[`OR1200_IMMU_PS-1:0]} : {icpu_vpn_r, icpu_adr_i[`OR1200_IMMU_PS-1:0]}; // DL: immu_en
assign qmemimmu_adr_o = immu_en & itlb_done ? {itlb_ppn, icpu_adr_i[`OR1200_IMMU_PS-1:2], 2'h0} : {icpu_vpn_r, icpu_adr_i[`OR1200_IMMU_PS-1:2], 2'h0}; 

reg     [31:0]                  spr_dat_reg;
//
// Output to SPRS unit
//
// spr_dat_o is registered on the 1st clock of spr read 
// so itlb can continue with process during execution of mfspr.
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		spr_dat_reg <=  32'h0000_0000;
	else if (spr_cs & !dis_spr_access_scnd_clk)
		spr_dat_reg <=  itlb_dat_o;

assign spr_dat_o = itlb_spr_access ? itlb_dat_o : spr_dat_reg; 

//
// Page fault exception logic
//
assign fault = itlb_done &
			(  (!supv & !itlb_uxe)		// Execute in user mode not enabled
			|| (supv & !itlb_sxe));		// Execute in supv mode not enabled

//
// TLB Miss exception logic
//
assign miss = itlb_done & !itlb_hit;

//
// ITLB Enable
//
assign itlb_en = immu_en & icpu_cycstb_i;

//
// Instantiation of ITLB
//
or1200_immu_tlb or1200_immu_tlb(
	// Rst and clk
        .clk(clk),
	.rst(rst),

        // I/F for translation
        .tlb_en(itlb_en),
	.vaddr(icpu_adr_i),
	.hit(itlb_hit),
	.ppn(itlb_ppn),
	.uxe(itlb_uxe),
	.sxe(itlb_sxe),
	.ci(itlb_ci),

`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(mbist_si_i),
	.mbist_so_o(mbist_so_o),
	.mbist_ctrl_i(mbist_ctrl_i),
`endif

        // SPR access
        .spr_cs(itlb_spr_access),
	.spr_write(spr_write),
	.spr_addr(spr_addr),
	.spr_dat_i(spr_dat_i),
	.spr_dat_o(itlb_dat_o)
);

`endif

endmodule
