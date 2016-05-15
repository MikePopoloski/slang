//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's VR, UPR and Configuration Registers                ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  According to OR1K architectural and OR1200 specifications.  ////
////                                                              ////
////  To Do:                                                      ////
////   - done                                                     ////
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
//
// $Log: or1200_cfgr.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_cfgr(
		   // RISC Internal Interface
		   spr_addr, spr_dat_o
		   );

   //
   // RISC Internal Interface
   //
   input	[31:0]	spr_addr;	// SPR Address
   output [31:0] 	spr_dat_o;	// SPR Read Data

   //
   // Internal wires & registers
   //
   reg [31:0] 		spr_dat_o;	// SPR Read Data

`ifdef OR1200_CFGR_IMPLEMENTED

   //
   // Implementation of VR, UPR and configuration registers
   //
   always @(spr_addr)
 `ifdef OR1200_SYS_FULL_DECODE
     if (~|spr_addr[31:4])
 `endif
       case(spr_addr[3:0])		// synopsys parallel_case
	 `OR1200_SPRGRP_SYS_VR: begin
	    spr_dat_o[`OR1200_VR_REV_BITS] = `OR1200_VR_REV;
	    spr_dat_o[`OR1200_VR_RES1_BITS] = `OR1200_VR_RES1;
	    spr_dat_o[`OR1200_VR_CFG_BITS] = `OR1200_VR_CFG;
	    spr_dat_o[`OR1200_VR_VER_BITS] = `OR1200_VR_VER;
	 end
	 `OR1200_SPRGRP_SYS_UPR: begin
	    spr_dat_o[`OR1200_UPR_UP_BITS] = `OR1200_UPR_UP;
	    spr_dat_o[`OR1200_UPR_DCP_BITS] = `OR1200_UPR_DCP;
	    spr_dat_o[`OR1200_UPR_ICP_BITS] = `OR1200_UPR_ICP;
	    spr_dat_o[`OR1200_UPR_DMP_BITS] = `OR1200_UPR_DMP;
	    spr_dat_o[`OR1200_UPR_IMP_BITS] = `OR1200_UPR_IMP;
	    spr_dat_o[`OR1200_UPR_MP_BITS] = `OR1200_UPR_MP;
	    spr_dat_o[`OR1200_UPR_DUP_BITS] = `OR1200_UPR_DUP;
	    spr_dat_o[`OR1200_UPR_PCUP_BITS] = `OR1200_UPR_PCUP;
	    spr_dat_o[`OR1200_UPR_PMP_BITS] = `OR1200_UPR_PMP;
	    spr_dat_o[`OR1200_UPR_PICP_BITS] = `OR1200_UPR_PICP;
	    spr_dat_o[`OR1200_UPR_TTP_BITS] = `OR1200_UPR_TTP;
	    spr_dat_o[`OR1200_UPR_FPP_BITS] = `OR1200_UPR_FPP;
	    spr_dat_o[`OR1200_UPR_RES1_BITS] = `OR1200_UPR_RES1;
	    spr_dat_o[`OR1200_UPR_CUP_BITS] = `OR1200_UPR_CUP;
	 end
	 `OR1200_SPRGRP_SYS_CPUCFGR: begin
	    spr_dat_o[`OR1200_CPUCFGR_NSGF_BITS] = `OR1200_CPUCFGR_NSGF;
	    spr_dat_o[`OR1200_CPUCFGR_HGF_BITS] = `OR1200_CPUCFGR_HGF;
	    spr_dat_o[`OR1200_CPUCFGR_OB32S_BITS] = `OR1200_CPUCFGR_OB32S;
	    spr_dat_o[`OR1200_CPUCFGR_OB64S_BITS] = `OR1200_CPUCFGR_OB64S;
	    spr_dat_o[`OR1200_CPUCFGR_OF32S_BITS] = `OR1200_CPUCFGR_OF32S;
	    spr_dat_o[`OR1200_CPUCFGR_OF64S_BITS] = `OR1200_CPUCFGR_OF64S;
	    spr_dat_o[`OR1200_CPUCFGR_OV64S_BITS] = `OR1200_CPUCFGR_OV64S;
	    spr_dat_o[`OR1200_CPUCFGR_RES1_BITS] = `OR1200_CPUCFGR_RES1;
	 end
	 `OR1200_SPRGRP_SYS_DMMUCFGR: begin
	    spr_dat_o[`OR1200_DMMUCFGR_NTW_BITS] = `OR1200_DMMUCFGR_NTW;
	    spr_dat_o[`OR1200_DMMUCFGR_NTS_BITS] = `OR1200_DMMUCFGR_NTS;
	    spr_dat_o[`OR1200_DMMUCFGR_NAE_BITS] = `OR1200_DMMUCFGR_NAE;
	    spr_dat_o[`OR1200_DMMUCFGR_CRI_BITS] = `OR1200_DMMUCFGR_CRI;
	    spr_dat_o[`OR1200_DMMUCFGR_PRI_BITS] = `OR1200_DMMUCFGR_PRI;
	    spr_dat_o[`OR1200_DMMUCFGR_TEIRI_BITS] = `OR1200_DMMUCFGR_TEIRI;
	    spr_dat_o[`OR1200_DMMUCFGR_HTR_BITS] = `OR1200_DMMUCFGR_HTR;
	    spr_dat_o[`OR1200_DMMUCFGR_RES1_BITS] = `OR1200_DMMUCFGR_RES1;
	 end
	 `OR1200_SPRGRP_SYS_IMMUCFGR: begin
	    spr_dat_o[`OR1200_IMMUCFGR_NTW_BITS] = `OR1200_IMMUCFGR_NTW;
	    spr_dat_o[`OR1200_IMMUCFGR_NTS_BITS] = `OR1200_IMMUCFGR_NTS;
	    spr_dat_o[`OR1200_IMMUCFGR_NAE_BITS] = `OR1200_IMMUCFGR_NAE;
	    spr_dat_o[`OR1200_IMMUCFGR_CRI_BITS] = `OR1200_IMMUCFGR_CRI;
	    spr_dat_o[`OR1200_IMMUCFGR_PRI_BITS] = `OR1200_IMMUCFGR_PRI;
	    spr_dat_o[`OR1200_IMMUCFGR_TEIRI_BITS] = `OR1200_IMMUCFGR_TEIRI;
	    spr_dat_o[`OR1200_IMMUCFGR_HTR_BITS] = `OR1200_IMMUCFGR_HTR;
	    spr_dat_o[`OR1200_IMMUCFGR_RES1_BITS] = `OR1200_IMMUCFGR_RES1;
	 end
	 `OR1200_SPRGRP_SYS_DCCFGR: begin
	    spr_dat_o[`OR1200_DCCFGR_NCW_BITS] = `OR1200_DCCFGR_NCW;
	    spr_dat_o[`OR1200_DCCFGR_NCS_BITS] = `OR1200_DCCFGR_NCS;
	    spr_dat_o[`OR1200_DCCFGR_CBS_BITS] = `OR1200_DCCFGR_CBS;
	    spr_dat_o[`OR1200_DCCFGR_CWS_BITS] = `OR1200_DCCFGR_CWS;
	    spr_dat_o[`OR1200_DCCFGR_CCRI_BITS] = `OR1200_DCCFGR_CCRI;
	    spr_dat_o[`OR1200_DCCFGR_CBIRI_BITS] = `OR1200_DCCFGR_CBIRI;
	    spr_dat_o[`OR1200_DCCFGR_CBPRI_BITS] = `OR1200_DCCFGR_CBPRI;
	    spr_dat_o[`OR1200_DCCFGR_CBLRI_BITS] = `OR1200_DCCFGR_CBLRI;
	    spr_dat_o[`OR1200_DCCFGR_CBFRI_BITS] = `OR1200_DCCFGR_CBFRI;
	    spr_dat_o[`OR1200_DCCFGR_CBWBRI_BITS] = `OR1200_DCCFGR_CBWBRI;
	    spr_dat_o[`OR1200_DCCFGR_RES1_BITS] = `OR1200_DCCFGR_RES1;
	 end
	 `OR1200_SPRGRP_SYS_ICCFGR: begin
	    spr_dat_o[`OR1200_ICCFGR_NCW_BITS] = `OR1200_ICCFGR_NCW;
	    spr_dat_o[`OR1200_ICCFGR_NCS_BITS] = `OR1200_ICCFGR_NCS;
	    spr_dat_o[`OR1200_ICCFGR_CBS_BITS] = `OR1200_ICCFGR_CBS;
	    spr_dat_o[`OR1200_ICCFGR_CWS_BITS] = `OR1200_ICCFGR_CWS;
	    spr_dat_o[`OR1200_ICCFGR_CCRI_BITS] = `OR1200_ICCFGR_CCRI;
	    spr_dat_o[`OR1200_ICCFGR_CBIRI_BITS] = `OR1200_ICCFGR_CBIRI;
	    spr_dat_o[`OR1200_ICCFGR_CBPRI_BITS] = `OR1200_ICCFGR_CBPRI;
	    spr_dat_o[`OR1200_ICCFGR_CBLRI_BITS] = `OR1200_ICCFGR_CBLRI;
	    spr_dat_o[`OR1200_ICCFGR_CBFRI_BITS] = `OR1200_ICCFGR_CBFRI;
	    spr_dat_o[`OR1200_ICCFGR_CBWBRI_BITS] = `OR1200_ICCFGR_CBWBRI;
	    spr_dat_o[`OR1200_ICCFGR_RES1_BITS] = `OR1200_ICCFGR_RES1;
	 end
	 `OR1200_SPRGRP_SYS_DCFGR: begin
	    spr_dat_o[`OR1200_DCFGR_NDP_BITS] = `OR1200_DCFGR_NDP;
	    spr_dat_o[`OR1200_DCFGR_WPCI_BITS] = `OR1200_DCFGR_WPCI;
	    spr_dat_o[`OR1200_DCFGR_RES1_BITS] = `OR1200_DCFGR_RES1;
	 end
	 default: spr_dat_o = 32'h0000_0000;
       endcase
 `ifdef OR1200_SYS_FULL_DECODE
     else
       spr_dat_o = 32'h0000_0000;
 `endif

`else

   //
   // When configuration registers are not implemented, only
   // implement VR and UPR
   //
   always @(spr_addr)
 `ifdef OR1200_SYS_FULL_DECODE
     if (spr_addr[31:4] == 28'h0)
 `endif
       case(spr_addr[3:0])
	 `OR1200_SPRGRP_SYS_VR: begin
	    spr_dat_o[`OR1200_VR_REV_BITS] = `OR1200_VR_REV;
	    spr_dat_o[`OR1200_VR_RES1_BITS] = `OR1200_VR_RES1;
	    spr_dat_o[`OR1200_VR_CFG_BITS] = `OR1200_VR_CFG;
	    spr_dat_o[`OR1200_VR_VER_BITS] = `OR1200_VR_VER;
	 end
	 `OR1200_SPRGRP_SYS_UPR: begin
	    spr_dat_o[`OR1200_UPR_UP_BITS] = `OR1200_UPR_UP;
	    spr_dat_o[`OR1200_UPR_DCP_BITS] = `OR1200_UPR_DCP;
	    spr_dat_o[`OR1200_UPR_ICP_BITS] = `OR1200_UPR_ICP;
	    spr_dat_o[`OR1200_UPR_DMP_BITS] = `OR1200_UPR_DMP;
	    spr_dat_o[`OR1200_UPR_IMP_BITS] = `OR1200_UPR_IMP;
	    spr_dat_o[`OR1200_UPR_MP_BITS] = `OR1200_UPR_MP;
	    spr_dat_o[`OR1200_UPR_DUP_BITS] = `OR1200_UPR_DUP;
	    spr_dat_o[`OR1200_UPR_PCUP_BITS] = `OR1200_UPR_PCUP;
	    spr_dat_o[`OR1200_UPR_PMP_BITS] = `OR1200_UPR_PMP;
	    spr_dat_o[`OR1200_UPR_PICP_BITS] = `OR1200_UPR_PICP;
	    spr_dat_o[`OR1200_UPR_TTP_BITS] = `OR1200_UPR_TTP;
	    spr_dat_o[`OR1200_UPR_RES1_BITS] = `OR1200_UPR_RES1;
	    spr_dat_o[`OR1200_UPR_CUP_BITS] = `OR1200_UPR_CUP;
	 end
	 default: spr_dat_o = 32'h0000_0000;
       endcase
 `ifdef OR1200_SYS_FULL_DECODE
     else
       spr_dat_o = 32'h0000_0000;
 `endif

`endif

endmodule
