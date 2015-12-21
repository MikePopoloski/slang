//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Power Management                                   ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  PM according to OR1K architectural specification.           ////
////                                                              ////
////  To Do:                                                      ////
////   - add support for dynamic clock gating                     ////
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
// $Log: or1200_pm.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 
//
// Revision 1.1  2002/01/03 08:16:15  lampret
// New prefixes for RTL files, prefixed module names. Updated cache controllers and MMUs.
//
// Revision 1.8  2001/10/21 17:57:16  lampret
// Removed params from generic_XX.v. Added translate_off/on in sprs.v and id.v. Removed spr_addr from dc.v and ic.v. Fixed CR+LF.
//
// Revision 1.7  2001/10/14 13:12:10  lampret
// MP3 version.
//
// Revision 1.1.1.1  2001/10/06 10:18:35  igorm
// no message
//
// Revision 1.2  2001/08/09 13:39:33  lampret
// Major clean-up.
//
// Revision 1.1  2001/07/20 00:46:21  lampret
// Development version of RTL. Libraries are missing.
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_pm(
	// RISC Internal Interface
	clk, rst, pic_wakeup, spr_write, spr_addr, spr_dat_i, spr_dat_o,
	
	// Power Management Interface
	pm_clksd, pm_cpustall, pm_dc_gate, pm_ic_gate, pm_dmmu_gate,
	pm_immu_gate, pm_tt_gate, pm_cpu_gate, pm_wakeup, pm_lvolt
);

//
// RISC Internal Interface
//
input		clk;		// Clock
input		rst;		// Reset
input		pic_wakeup;	// Wakeup from the PIC
input		spr_write;	// SPR Read/Write
input	[31:0]	spr_addr;	// SPR Address
input	[31:0]	spr_dat_i;	// SPR Write Data
output	[31:0]	spr_dat_o;	// SPR Read Data

//
// Power Management Interface
//
input		pm_cpustall;	// Stall the CPU
output	[3:0]	pm_clksd;	// Clock Slowdown factor
output		pm_dc_gate;	// Gate DCache clock
output		pm_ic_gate;	// Gate ICache clock
output		pm_dmmu_gate;	// Gate DMMU clock
output		pm_immu_gate;	// Gate IMMU clock
output		pm_tt_gate;	// Gate Tick Timer clock
output		pm_cpu_gate;	// Gate main RISC/CPU clock
output		pm_wakeup;	// Activate (de-gate) all clocks
output		pm_lvolt;	// Lower operating voltage

`ifdef OR1200_PM_IMPLEMENTED

//
// Power Management Register bits
//
reg	[3:0]	sdf;	// Slow-down factor
reg		dme;	// Doze Mode Enable
reg		sme;	// Sleep Mode Enable
reg		dcge;	// Dynamic Clock Gating Enable

//
// Internal wires
//
wire		pmr_sel; // PMR select

//
// PMR address decoder (partial decoder)
//
`ifdef OR1200_PM_PARTIAL_DECODING
assign pmr_sel = (spr_addr[`OR1200_SPR_GROUP_BITS] == `OR1200_SPRGRP_PM) ? 1'b1 : 1'b0;
`else
assign pmr_sel = ((spr_addr[`OR1200_SPR_GROUP_BITS] == `OR1200_SPRGRP_PM) &&
		  (spr_addr[`OR1200_SPR_OFS_BITS] == `OR1200_PM_OFS_PMR)) ? 1'b1 : 1'b0;
`endif

//
// Write to PMR and also PMR[DME]/PMR[SME] reset when
// pic_wakeup is asserted
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		{dcge, sme, dme, sdf} <= 7'b0;
	else if (pmr_sel && spr_write) begin
		sdf <=  spr_dat_i[`OR1200_PM_PMR_SDF];
		dme <=  spr_dat_i[`OR1200_PM_PMR_DME];
		sme <=  spr_dat_i[`OR1200_PM_PMR_SME];
		dcge <=  spr_dat_i[`OR1200_PM_PMR_DCGE];
	end
	else if (pic_wakeup) begin
		dme <=  1'b0;
		sme <=  1'b0;
	end

//
// Read PMR
//
`ifdef OR1200_PM_READREGS
assign spr_dat_o[`OR1200_PM_PMR_SDF] = sdf;
assign spr_dat_o[`OR1200_PM_PMR_DME] = dme;
assign spr_dat_o[`OR1200_PM_PMR_SME] = sme;
assign spr_dat_o[`OR1200_PM_PMR_DCGE] = dcge;
`ifdef OR1200_PM_UNUSED_ZERO
assign spr_dat_o[`OR1200_PM_PMR_UNUSED] = 25'b0;
`endif
`endif

//
// Generate pm_clksd
//
assign pm_clksd = sdf;

//
// Statically generate all clock gate outputs
// TODO: add dynamic clock gating feature
//
assign pm_cpu_gate = (dme | sme) & ~pic_wakeup;
assign pm_dc_gate = pm_cpu_gate;
assign pm_ic_gate = pm_cpu_gate;
assign pm_dmmu_gate = pm_cpu_gate;
assign pm_immu_gate = pm_cpu_gate;
assign pm_tt_gate = sme & ~pic_wakeup;

//
// Assert pm_wakeup when pic_wakeup is asserted
//
assign pm_wakeup = pic_wakeup;

//
// Assert pm_lvolt when pm_cpu_gate or pm_cpustall are asserted
//
assign pm_lvolt = pm_cpu_gate | pm_cpustall;

`else

//
// When PM is not implemented, drive all outputs as would when PM is disabled
//
assign pm_clksd = 4'b0;
assign pm_cpu_gate = 1'b0;
assign pm_dc_gate = 1'b0;
assign pm_ic_gate = 1'b0;
assign pm_dmmu_gate = 1'b0;
assign pm_immu_gate = 1'b0;
assign pm_tt_gate = 1'b0;
assign pm_wakeup = 1'b1;
assign pm_lvolt = 1'b0;

//
// Read PMR
//
`ifdef OR1200_PM_READREGS
assign spr_dat_o[`OR1200_PM_PMR_SDF] = 4'b0;
assign spr_dat_o[`OR1200_PM_PMR_DME] = 1'b0;
assign spr_dat_o[`OR1200_PM_PMR_SME] = 1'b0;
assign spr_dat_o[`OR1200_PM_PMR_DCGE] = 1'b0;
`ifdef OR1200_PM_UNUSED_ZERO
assign spr_dat_o[`OR1200_PM_PMR_UNUSED] = 25'b0;
`endif
`endif

`endif

endmodule
