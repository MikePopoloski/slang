//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's interface to SPRs                                  ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Decoding of SPR addresses and access to SPRs                ////
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
// $Log: or1200_sprs.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Major update: 
// Structure reordered and bugs fixed. 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_sprs(
		   // Clk & Rst
		   clk, rst,

		   // Internal CPU interface
		   flagforw, flag_we, flag, cyforw, cy_we, carry,
		   ovforw, ov_we, dsx,
		   addrbase, addrofs, dat_i, branch_op, ex_spr_read, 
		   ex_spr_write, 
		   epcr, eear, esr, except_started,
		   to_wbmux, epcr_we, eear_we, esr_we, pc_we, sr_we, to_sr, sr,
		   spr_dat_cfgr, spr_dat_rf, spr_dat_npc, spr_dat_ppc, 
		   spr_dat_mac,
		   
		   boot_adr_sel_i,

		   // Floating point SPR input
		   fpcsr, fpcsr_we, spr_dat_fpu,

		   // From/to other RISC units
		   spr_dat_pic, spr_dat_tt, spr_dat_pm,
		   spr_dat_dmmu, spr_dat_immu, spr_dat_du,
		   spr_addr, spr_dat_o, spr_cs, spr_we,

		   du_addr, du_dat_du, du_read,
		   du_write, du_dat_cpu

		   );

   parameter width = `OR1200_OPERAND_WIDTH;

   //
   // I/O Ports
   //

   //
   // Internal CPU interface
   //
   input				clk; 		// Clock
   input 				rst;		// Reset
   input 				flagforw;	// From ALU
   input 				flag_we;	// From ALU
   output 				flag;		// SR[F]
   input 				cyforw;		// From ALU
   input 				cy_we;		// From ALU
   output 				carry;		// SR[CY]
   input 				ovforw;		// From ALU
   input 				ov_we;		// From ALU
   input                                dsx;            // From except
   input [width-1:0] 			addrbase;	// SPR base address
   input [15:0] 			addrofs;	// SPR offset
   input [width-1:0] 			dat_i;		// SPR write data
   input 				ex_spr_read;	// l.mfspr in EX
   input 				ex_spr_write;	// l.mtspr in EX
   input [`OR1200_BRANCHOP_WIDTH-1:0] 	branch_op;	// Branch operation
   input [width-1:0] 			epcr /* verilator public */;// EPCR0
   input [width-1:0] 			eear /* verilator public */;// EEAR0
   input [`OR1200_SR_WIDTH-1:0] 	esr /* verilator public */; // ESR0
   input 				except_started; // Exception was started
   output [width-1:0] 			to_wbmux;	// For l.mfspr
   output				epcr_we;	// EPCR0 write enable
   output				eear_we;	// EEAR0 write enable
   output				esr_we;		// ESR0 write enable
   output				pc_we;		// PC write enable
   output 				sr_we;		// Write enable SR
   output [`OR1200_SR_WIDTH-1:0] 	to_sr;		// Data to SR
   output [`OR1200_SR_WIDTH-1:0] 	sr /* verilator public */;// SR
   input [31:0] 			spr_dat_cfgr;	// Data from CFGR
   input [31:0] 			spr_dat_rf;	// Data from RF
   input [31:0] 			spr_dat_npc;	// Data from NPC
   input [31:0] 			spr_dat_ppc;	// Data from PPC   
   input [31:0] 			spr_dat_mac;	// Data from MAC
   input				boot_adr_sel_i;

   input [`OR1200_FPCSR_WIDTH-1:0] 	fpcsr;	// FPCSR
   output 				fpcsr_we;	// Write enable FPCSR   
   input [31:0] 			spr_dat_fpu;    // Data from FPU
   
   //
   // To/from other RISC units
   //
   input [31:0] 			spr_dat_pic;	// Data from PIC
   input [31:0] 			spr_dat_tt;	// Data from TT
   input [31:0] 			spr_dat_pm;	// Data from PM
   input [31:0] 			spr_dat_dmmu;	// Data from DMMU
   input [31:0] 			spr_dat_immu;	// Data from IMMU
   input [31:0] 			spr_dat_du;	// Data from DU
   output [31:0] 			spr_addr;	// SPR Address
   output [31:0] 			spr_dat_o;	// Data to unit
   output [31:0] 			spr_cs;		// Unit select
   output				spr_we;		// SPR write enable

   //
   // To/from Debug Unit
   //
   input [width-1:0] 			du_addr;	// Address
   input [width-1:0] 			du_dat_du;	// Data from DU to SPRS
   input				du_read;	// Read qualifier
   input				du_write;	// Write qualifier
   output [width-1:0] 			du_dat_cpu;	// Data from SPRS to DU

   //
   // Internal regs & wires
   //
   reg [`OR1200_SR_WIDTH-1:0] 		sr_reg;		// SR
   reg 					sr_reg_bit_eph;	// SR_EPH bit
   reg 					sr_reg_bit_eph_select;// SR_EPH select
   wire 				sr_reg_bit_eph_muxed;// SR_EPH muxed bit
   reg [`OR1200_SR_WIDTH-1:0] 		sr;			// SR
   reg [width-1:0] 			to_wbmux;	// For l.mfspr
   wire 				cfgr_sel;	// Select for cfg regs
   wire 				rf_sel;		// Select for RF
   wire 				npc_sel;	// Select for NPC
   wire 				ppc_sel;	// Select for PPC
   wire 				sr_sel;		// Select for SR	
   wire 				epcr_sel;	// Select for EPCR0
   wire 				eear_sel;	// Select for EEAR0
   wire 				esr_sel;	// Select for ESR0
   wire 				fpcsr_sel;	// Select for FPCSR   
   wire [31:0] 				sys_data;// Read data from system SPRs
   wire 				du_access;// Debug unit access
   reg [31:0] 				unqualified_cs;	// Unqualified selects
   wire 				ex_spr_write; // jb
   
   //
   // Decide if it is debug unit access
   //
   assign du_access = du_read | du_write;

   //
   // Generate SPR address from base address and offset
   // OR from debug unit address
   //
   assign spr_addr = du_access ? du_addr : (addrbase | {16'h0000, addrofs});

   //
   // SPR is written by debug unit or by l.mtspr
   //
   assign spr_dat_o = du_write ? du_dat_du : dat_i;

   //
   // debug unit data input:
   //  - read of SPRS by debug unit
   //  - write into debug unit SPRs by debug unit itself
   //  - write into debug unit SPRs by l.mtspr
   //
   assign du_dat_cpu = du_read ? to_wbmux : du_write ? du_dat_du : dat_i;

   //
   // Write into SPRs when DU or l.mtspr
   //
   assign spr_we = du_write | ( ex_spr_write & !du_access );


   //
   // Qualify chip selects
   //
   assign spr_cs = unqualified_cs & {32{du_read | du_write | ex_spr_read | 
					(ex_spr_write & sr[`OR1200_SR_SM])}};

   //
   // Decoding of groups
   //
   always @(spr_addr)
     case (spr_addr[`OR1200_SPR_GROUP_BITS])	// synopsys parallel_case
       `OR1200_SPR_GROUP_WIDTH'd00: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000001;
       `OR1200_SPR_GROUP_WIDTH'd01: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000010;
       `OR1200_SPR_GROUP_WIDTH'd02: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00000100;
       `OR1200_SPR_GROUP_WIDTH'd03: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00001000;
       `OR1200_SPR_GROUP_WIDTH'd04: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00010000;
       `OR1200_SPR_GROUP_WIDTH'd05: unqualified_cs 
	 = 32'b00000000_00000000_00000000_00100000;
       `OR1200_SPR_GROUP_WIDTH'd06: unqualified_cs 
	 = 32'b00000000_00000000_00000000_01000000;
       `OR1200_SPR_GROUP_WIDTH'd07: unqualified_cs 
	 = 32'b00000000_00000000_00000000_10000000;
       `OR1200_SPR_GROUP_WIDTH'd08: unqualified_cs 
	 = 32'b00000000_00000000_00000001_00000000;
       `OR1200_SPR_GROUP_WIDTH'd09: unqualified_cs 
	 = 32'b00000000_00000000_00000010_00000000;
       `OR1200_SPR_GROUP_WIDTH'd10: unqualified_cs 
	 = 32'b00000000_00000000_00000100_00000000;
       `OR1200_SPR_GROUP_WIDTH'd11: unqualified_cs 
	 = 32'b00000000_00000000_00001000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd12: unqualified_cs 
	 = 32'b00000000_00000000_00010000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd13: unqualified_cs 
	 = 32'b00000000_00000000_00100000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd14: unqualified_cs 
	 = 32'b00000000_00000000_01000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd15: unqualified_cs 
	 = 32'b00000000_00000000_10000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd16: unqualified_cs 
	 = 32'b00000000_00000001_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd17: unqualified_cs 
	 = 32'b00000000_00000010_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd18: unqualified_cs 
	 = 32'b00000000_00000100_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd19: unqualified_cs 
	 = 32'b00000000_00001000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd20: unqualified_cs 
	 = 32'b00000000_00010000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd21: unqualified_cs 
	 = 32'b00000000_00100000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd22: unqualified_cs 
	 = 32'b00000000_01000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd23: unqualified_cs 
	 = 32'b00000000_10000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd24: unqualified_cs 
	 = 32'b00000001_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd25: unqualified_cs 
	 = 32'b00000010_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd26: unqualified_cs 
	 = 32'b00000100_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd27: unqualified_cs 
	 = 32'b00001000_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd28: unqualified_cs 
	 = 32'b00010000_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd29: unqualified_cs 
	 = 32'b00100000_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd30: unqualified_cs 
	 = 32'b01000000_00000000_00000000_00000000;
       `OR1200_SPR_GROUP_WIDTH'd31: unqualified_cs 
	 = 32'b10000000_00000000_00000000_00000000;
     endcase

   //
   // SPRs System Group
   //

   //
   // What to write into SR
   //
   assign to_sr[`OR1200_SR_FO:`OR1200_SR_OVE] 
	    = (except_started) ? {sr[`OR1200_SR_FO:`OR1200_SR_EPH],dsx,1'b0} :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? 
	      esr[`OR1200_SR_FO:`OR1200_SR_OVE] : (spr_we && sr_sel) ? 
	      {1'b1, spr_dat_o[`OR1200_SR_FO-1:`OR1200_SR_OVE]} :
	      sr[`OR1200_SR_FO:`OR1200_SR_OVE];
   assign to_sr[`OR1200_SR_TED] 
	    = (except_started) ? 1'b1 :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? esr[`OR1200_SR_TED] :
	      (spr_we && sr_sel) ? spr_dat_o[`OR1200_SR_TED] :
	      sr[`OR1200_SR_TED];
   assign to_sr[`OR1200_SR_OV] 
	    = (except_started) ? sr[`OR1200_SR_OV] :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? esr[`OR1200_SR_OV] :
	      ov_we ? ovforw :
	      (spr_we && sr_sel) ? spr_dat_o[`OR1200_SR_OV] :
	      sr[`OR1200_SR_OV];
   assign to_sr[`OR1200_SR_CY] 
	    = (except_started) ? sr[`OR1200_SR_CY] :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? esr[`OR1200_SR_CY] :
	      cy_we ? cyforw :
	      (spr_we && sr_sel) ? spr_dat_o[`OR1200_SR_CY] :
	      sr[`OR1200_SR_CY];
   assign to_sr[`OR1200_SR_F] 
	    = (except_started) ? sr[`OR1200_SR_F] :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? esr[`OR1200_SR_F] :
	      flag_we ? flagforw :
	      (spr_we && sr_sel) ? spr_dat_o[`OR1200_SR_F] :
	      sr[`OR1200_SR_F];
   
   assign to_sr[`OR1200_SR_CE:`OR1200_SR_SM] 
	    = (except_started) ? {sr[`OR1200_SR_CE:`OR1200_SR_LEE], 2'b00, 
				  sr[`OR1200_SR_ICE:`OR1200_SR_DCE], 3'b001} :
	      (branch_op == `OR1200_BRANCHOP_RFE) ? 
	      esr[`OR1200_SR_CE:`OR1200_SR_SM] : (spr_we && sr_sel) ? 
	      spr_dat_o[`OR1200_SR_CE:`OR1200_SR_SM] :
	      sr[`OR1200_SR_CE:`OR1200_SR_SM];

   //
   // Selects for system SPRs
   //
   assign cfgr_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		      (spr_addr[10:4] == `OR1200_SPR_CFGR));
   assign rf_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		    (spr_addr[10:5] == `OR1200_SPR_RF));
   assign npc_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		     (spr_addr[10:0] == `OR1200_SPR_NPC));
   assign ppc_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		     (spr_addr[10:0] == `OR1200_SPR_PPC));
   assign sr_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		    (spr_addr[10:0] == `OR1200_SPR_SR));
   assign epcr_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		      (spr_addr[10:0] == `OR1200_SPR_EPCR));
   assign eear_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		      (spr_addr[10:0] == `OR1200_SPR_EEAR));
   assign esr_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		     (spr_addr[10:0] == `OR1200_SPR_ESR));
   assign fpcsr_sel = (spr_cs[`OR1200_SPR_GROUP_SYS] && 
		       (spr_addr[10:0] == `OR1200_SPR_FPCSR));


   //
   // Write enables for system SPRs
   //
   assign sr_we = (spr_we && sr_sel) | (branch_op == `OR1200_BRANCHOP_RFE) | 
		  flag_we | cy_we | ov_we;
   assign pc_we = (du_write && (npc_sel | ppc_sel));
   assign epcr_we = (spr_we && epcr_sel);
   assign eear_we = (spr_we && eear_sel);
   assign esr_we = (spr_we && esr_sel);
   assign fpcsr_we = (spr_we && fpcsr_sel);
   
   //
   // Output from system SPRs
   //
   assign sys_data = (spr_dat_cfgr & {32{cfgr_sel}}) |
		     (spr_dat_rf & {32{rf_sel}}) |
		     (spr_dat_npc & {32{npc_sel}}) |
		     (spr_dat_ppc & {32{ppc_sel}}) |
		     ({{32-`OR1200_SR_WIDTH{1'b0}},sr} & {32{sr_sel}}) |
		     (epcr & {32{epcr_sel}}) |
		     (eear & {32{eear_sel}}) |
		     ({{32-`OR1200_FPCSR_WIDTH{1'b0}},fpcsr} & 
		      {32{fpcsr_sel}}) |
		     ({{32-`OR1200_SR_WIDTH{1'b0}},esr} & {32{esr_sel}});

   //
   // Flag alias
   //
   assign flag = sr[`OR1200_SR_F];

   //
   // Carry alias
   //
   assign carry = sr[`OR1200_SR_CY];
   
   //
   // Supervision register
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       sr_reg <=  {2'b01, // Fixed one.
		   `OR1200_SR_EPH_DEF, {`OR1200_SR_WIDTH-4{1'b0}}, 1'b1};
     else if (except_started)
       sr_reg <=  to_sr[`OR1200_SR_WIDTH-1:0];
     else if (sr_we)
       sr_reg <=  to_sr[`OR1200_SR_WIDTH-1:0];

   // EPH part of Supervision register
   always @(posedge clk or `OR1200_RST_EVENT rst)
     // default value 
     if (rst == `OR1200_RST_VALUE) begin
	sr_reg_bit_eph <=  `OR1200_SR_EPH_DEF;
	// select async. value due to reset state
	sr_reg_bit_eph_select <=  1'b1;	
     end
   // selected value (different from default) is written into FF after reset 
   // state
     else if (sr_reg_bit_eph_select) begin
	// dynamic value can only be assigned to FF out of reset!
	sr_reg_bit_eph <=  boot_adr_sel_i;
	sr_reg_bit_eph_select <=  1'b0;	// select FF value
     end
     else if (sr_we) begin
	sr_reg_bit_eph <=  to_sr[`OR1200_SR_EPH];
     end

   // select async. value of EPH bit after reset 
   assign	sr_reg_bit_eph_muxed = (sr_reg_bit_eph_select) ? 
				       boot_adr_sel_i : sr_reg_bit_eph;

   // EPH part joined together with rest of Supervision register
   always @(sr_reg or sr_reg_bit_eph_muxed)
     sr = {sr_reg[`OR1200_SR_WIDTH-1:`OR1200_SR_WIDTH-2], sr_reg_bit_eph_muxed,
	   sr_reg[`OR1200_SR_WIDTH-4:0]};

`ifdef verilator
   // Function to access various sprs (for Verilator). Have to hide this from
   // simulator, since functions with no inputs are not allowed in IEEE
   // 1364-2001.

   function [31:0] get_sr;
      // verilator public
      get_sr = {{32-`OR1200_SR_WIDTH{1'b0}},sr};
   endfunction // get_sr

   function [31:0] get_epcr;
      // verilator public
      get_epcr = epcr;
   endfunction // get_epcr

   function [31:0] get_eear;
      // verilator public
      get_eear = eear;
   endfunction // get_eear

   function [31:0] get_esr;
      // verilator public
      get_esr = {{32-`OR1200_SR_WIDTH{1'b0}},esr};
   endfunction // get_esr

`endif
   
   //
   // MTSPR/MFSPR interface
   //
   always @(spr_addr or sys_data or spr_dat_mac or spr_dat_pic or spr_dat_pm or
	    spr_dat_fpu or
	    spr_dat_dmmu or spr_dat_immu or spr_dat_du or spr_dat_tt) begin
      casez (spr_addr[`OR1200_SPR_GROUP_BITS]) // synopsys parallel_case
	`OR1200_SPR_GROUP_SYS:
	  to_wbmux = sys_data;
	`OR1200_SPR_GROUP_TT:
	  to_wbmux = spr_dat_tt;
	`OR1200_SPR_GROUP_PIC:
	  to_wbmux = spr_dat_pic;
	`OR1200_SPR_GROUP_PM:
	  to_wbmux = spr_dat_pm;
	`OR1200_SPR_GROUP_DMMU:
	  to_wbmux = spr_dat_dmmu;
	`OR1200_SPR_GROUP_IMMU:
	  to_wbmux = spr_dat_immu;
	`OR1200_SPR_GROUP_MAC:
	  to_wbmux = spr_dat_mac;
	`OR1200_SPR_GROUP_FPU:
	  to_wbmux = spr_dat_fpu;
	default: //`OR1200_SPR_GROUP_DU:
	  to_wbmux = spr_dat_du;
      endcase
   end

endmodule
