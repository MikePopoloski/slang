//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's generate PC                                        ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  PC, interface to IC.                                        ////
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
// $Log: or1200_genpc.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Major update: 
// Structure reordered and bugs fixed. 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_genpc(
	// Clock and reset
	clk, rst,

	// External i/f to IC
	icpu_adr_o, icpu_cycstb_o, icpu_sel_o, icpu_tag_o,
	icpu_rty_i, icpu_adr_i,

	// Internal i/f
	pre_branch_op, branch_op, except_type, except_prefix,
	id_branch_addrtarget, ex_branch_addrtarget, muxed_b, operand_b, 
	flag, flagforw, ex_branch_taken, except_start,
	epcr, spr_dat_i, spr_pc_we, genpc_refetch,
	genpc_freeze, no_more_dslot, lsu_stall, du_flush_pipe, spr_dat_npc
);

//
// I/O
//

//
// Clock and reset
//
input				clk;
input				rst;

//
// External i/f to IC
//
output	[31:0]			icpu_adr_o;
output				icpu_cycstb_o;
output	[3:0]			icpu_sel_o;
output	[3:0]			icpu_tag_o;
input				icpu_rty_i;
input	[31:0]			icpu_adr_i;

//
// Internal i/f
//
input   [`OR1200_BRANCHOP_WIDTH-1:0]    pre_branch_op;
input	[`OR1200_BRANCHOP_WIDTH-1:0]	branch_op;
input	[`OR1200_EXCEPT_WIDTH-1:0]	except_type;
input					except_prefix;
input	[31:2]			id_branch_addrtarget;
input	[31:2]			ex_branch_addrtarget;
input	[31:0]			muxed_b;
input	[31:0]			operand_b;
input				flag;
input				flagforw;
output				ex_branch_taken;
input				except_start;
input	[31:0]			epcr;
input	[31:0]			spr_dat_i;
input				spr_pc_we;
input [31:0] 			spr_dat_npc;
input				genpc_refetch;
input				genpc_freeze;
input				no_more_dslot;
input				lsu_stall;
input				du_flush_pipe;

parameter boot_adr = `OR1200_BOOT_ADR;
//
// Internal wires and regs
//
reg	[31:2]			pcreg_default;
reg				pcreg_select;
reg	[31:2]			pcreg;
reg	[31:0]			pc;
// Set in event of jump or taken branch   
reg				ex_branch_taken;
reg				genpc_refetch_r;
reg				wait_lsu;

   //
   // Address of insn to be fecthed
   //
   assign icpu_adr_o = !no_more_dslot & !except_start & !spr_pc_we & !du_flush_pipe
		       & (icpu_rty_i | genpc_refetch) ? 
		       icpu_adr_i : {pc[31:2], 1'b0, ex_branch_taken|spr_pc_we};

   //
   // Control access to IC subsystem
   //
   assign icpu_cycstb_o = ~(genpc_freeze | (|pre_branch_op && !icpu_rty_i) | wait_lsu);
   assign icpu_sel_o = 4'b1111;
   assign icpu_tag_o = `OR1200_ITAG_NI;

   //
   // wait_lsu
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       wait_lsu <=  1'b0;
     else if (!wait_lsu & |pre_branch_op & lsu_stall)
       wait_lsu <=  1'b1;
     else if (wait_lsu & ~|pre_branch_op)
       wait_lsu <=  1'b0;

   //
   // genpc_freeze_r
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       genpc_refetch_r <=  1'b0;
     else if (genpc_refetch)
       genpc_refetch_r <=  1'b1;
     else
       genpc_refetch_r <=  1'b0;

   //
   // Async calculation of new PC value. This value is used for addressing the
   // IC.
   //
   always @(pcreg or ex_branch_addrtarget or flag or branch_op or except_type
	    or except_start or operand_b or epcr or spr_pc_we or spr_dat_i or 
	    except_prefix or du_flush_pipe) 
     begin
	casez ({du_flush_pipe, spr_pc_we, except_start, branch_op}) // synopsys parallel_case
	  {3'b000, `OR1200_BRANCHOP_NOP}: begin
	     pc = {pcreg + 30'd1, 2'b0};
	     ex_branch_taken = 1'b0;
	  end
	  {3'b000, `OR1200_BRANCHOP_J}: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("%t: BRANCHOP_J: pc <= ex_branch_addrtarget %h"
		      , $time, ex_branch_addrtarget);
	     // synopsys translate_on
`endif
	     pc = {ex_branch_addrtarget, 2'b00};
	     ex_branch_taken = 1'b1;
	  end
	  {3'b000, `OR1200_BRANCHOP_JR}: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("%t: BRANCHOP_JR: pc <= operand_b %h", 
		      $time, operand_b);
	     // synopsys translate_on
`endif
	     pc = operand_b;
	     ex_branch_taken = 1'b1;
	  end
	  {3'b000, `OR1200_BRANCHOP_BF}:
	    if (flag) begin
`ifdef OR1200_VERBOSE
	       // synopsys translate_off
	       $display("%t: BRANCHOP_BF: pc <= ex_branch_addrtarget %h", 
			$time, ex_branch_addrtarget);
	       // synopsys translate_on
`endif
	       pc = {ex_branch_addrtarget, 2'b00};
	       ex_branch_taken = 1'b1;
	    end
	    else begin
`ifdef OR1200_VERBOSE
	       // synopsys translate_off
	       $display("%t: BRANCHOP_BF: not taken", $time);
	       // synopsys translate_on
`endif
	       pc = {pcreg + 30'd1, 2'b0};
	       ex_branch_taken = 1'b0;
	    end
	  {3'b000, `OR1200_BRANCHOP_BNF}:
	    if (flag) begin
`ifdef OR1200_VERBOSE
	       // synopsys translate_off
	       $display("%t: BRANCHOP_BNF: not taken", $time);
	       // synopsys translate_on
`endif
	       pc = {pcreg + 30'd1, 2'b0};
	       ex_branch_taken = 1'b0;
	    end
	    else begin
`ifdef OR1200_VERBOSE
	       // synopsys translate_off
	       $display("%t: BRANCHOP_BNF: pc <= ex_branch_addrtarget %h", 
			$time, ex_branch_addrtarget);
	       // synopsys translate_on
`endif
	       pc = {ex_branch_addrtarget, 2'b00};
	       ex_branch_taken = 1'b1;
	    end
	  {3'b000, `OR1200_BRANCHOP_RFE}: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("%t: BRANCHOP_RFE: pc <= epcr %h", 
		      $time, epcr);
	     // synopsys translate_on
`endif
	     pc = epcr;
	     ex_branch_taken = 1'b1;
	  end
	  {3'b100, 3'b???}: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("Reload breaked ins at : %h.", spr_dat_npc);
	     // synopsys translate_on
`endif
	     pc = spr_dat_npc;
	     ex_branch_taken = 1'b1;
	  end
	  {3'b001, 3'b???}: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("Starting exception: %h.", except_type);
	     // synopsys translate_on
`endif
	     pc = {(except_prefix ? 
		    `OR1200_EXCEPT_EPH1_P : `OR1200_EXCEPT_EPH0_P), 
		   except_type, `OR1200_EXCEPT_V};
	     ex_branch_taken = 1'b1;
	  end
	  default: begin
`ifdef OR1200_VERBOSE
	     // synopsys translate_off
	     $display("l.mtspr writing into PC: %h.", spr_dat_i);
	     // synopsys translate_on
`endif
	     pc = spr_dat_i;
	     ex_branch_taken = 1'b0;
	  end
	endcase
     end

   // select async. value for pcreg after reset - PC jumps to the address selected
   // after boot.
   wire [31:0] pcreg_boot = boot_adr;

   //
   // PC register
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     // default value 
     if (rst == `OR1200_RST_VALUE) begin
	pcreg_default <=  (boot_adr >>2) - 4;
	pcreg_select <=  1'b1;// select async. value due to reset state
     end
   // selected value (different from default) is written into FF after
   // reset state
     else if (pcreg_select) begin
	// dynamic value can only be assigned to FF out of reset! 
	pcreg_default <=  pcreg_boot[31:2];	
	pcreg_select <=  1'b0;		// select FF value 
     end
     else if (spr_pc_we) begin
	pcreg_default <=  spr_dat_i[31:2];
     end
     else if (du_flush_pipe | no_more_dslot | except_start | !genpc_freeze & !icpu_rty_i 
	      & !genpc_refetch) begin
	pcreg_default <=  pc[31:2];
     end

   always @(pcreg_boot or pcreg_default or pcreg_select)
     if (pcreg_select)
       // async. value is selected due to reset state 
       pcreg = pcreg_boot[31:2];
     else
       // FF value is selected 2nd clock after reset state 
       pcreg = pcreg_default ;

endmodule
