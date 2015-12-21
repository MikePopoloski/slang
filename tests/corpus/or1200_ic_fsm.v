//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's IC FSM                                             ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Insn cache state machine                                    ////
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
// $Log: or1200_ic_fsm.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

`define OR1200_ICFSM_IDLE	2'd0
`define OR1200_ICFSM_CFETCH	2'd1
`define OR1200_ICFSM_LREFILL3	2'd2
`define OR1200_ICFSM_IFETCH	2'd3

//
// Instruction cache FSM
//

module or1200_ic_fsm(
	// Clock and reset
	clk, rst,

	// Internal i/f to top level IC
	ic_en, icqmem_cycstb_i, icqmem_ci_i,
	tagcomp_miss, 
	biudata_valid, biudata_error, 
        start_addr, saved_addr,
	icram_we, tag_we,
        biu_read, 
        first_hit_ack, first_miss_ack, first_miss_err,
	burst
);

//
// I/O
//
input				clk;
input				rst;
input				ic_en;
input				icqmem_cycstb_i;
input				icqmem_ci_i;
input				tagcomp_miss;
input				biudata_valid;
input				biudata_error;
input	[31:0]			start_addr;
output	[31:0]			saved_addr;
output	[3:0]			icram_we;
output				biu_read;
output				first_hit_ack;
output				first_miss_ack;
output				first_miss_err;
output				burst;
output				tag_we;

//
// Internal wires and regs
//
reg	[31:0]			saved_addr_r;
reg	[1:0]			state;
reg [`OR1200_ICLS-1:0]    	cnt;
reg				hitmiss_eval;
reg				load;
reg				cache_inhibit;
reg 				last_eval_miss; // JPB
   
   //
   // Generate of ICRAM write enables
   //
   assign icram_we = {4{biu_read & biudata_valid & !cache_inhibit}};
   assign tag_we = biu_read & biudata_valid & !cache_inhibit;

   //
   // BIU read and write
   //
   assign biu_read = (hitmiss_eval & tagcomp_miss) | (!hitmiss_eval & load);

   //assign saved_addr = hitmiss_eval ? start_addr : saved_addr_r;
   assign saved_addr = saved_addr_r;

   // Asserted when a cache hit occurs and the first word is ready/valid
   assign first_hit_ack = (state == `OR1200_ICFSM_CFETCH) & hitmiss_eval & 
			  !tagcomp_miss & !cache_inhibit;

   // Asserted when a cache miss occurs, but the first word of the new
   // cache line is ready (on the bus)
   // Cache hits overpower bus data
   assign first_miss_ack = (state == `OR1200_ICFSM_CFETCH) & biudata_valid &
			   ~first_hit_ack;
   
   // Asserted when a cache occurs, but there was a bus error with handling
   // the old line or fetching the new line
   assign first_miss_err = (state == `OR1200_ICFSM_CFETCH) & biudata_error;

   //
   // Assert burst when doing reload of complete cache line
   //
   assign burst = (state == `OR1200_ICFSM_CFETCH) & tagcomp_miss & 
		  !cache_inhibit | (state == `OR1200_ICFSM_LREFILL3);

   //
   // Main IC FSM
   //
   always @(posedge clk or `OR1200_RST_EVENT rst) begin
      if (rst == `OR1200_RST_VALUE) begin
	 state <=  `OR1200_ICFSM_IDLE;
	 saved_addr_r <=  32'b0;
	 hitmiss_eval <=  1'b0;
	 load <=  1'b0;
	 cnt <=  `OR1200_ICLS'd0;
	 cache_inhibit <=  1'b0;
	 last_eval_miss <= 0; // JPB
	 
      end
      else
	case (state)	// synopsys parallel_case
	  `OR1200_ICFSM_IDLE :
	    if (ic_en & icqmem_cycstb_i) begin		// fetch
	       state <=  `OR1200_ICFSM_CFETCH;
	       saved_addr_r <=  start_addr;
	       hitmiss_eval <=  1'b1;
	       load <=  1'b1;
	       cache_inhibit <=  icqmem_ci_i;
	       last_eval_miss <= 0; // JPB
	    end
	    else begin			// idle
	       hitmiss_eval <=  1'b0;
	       load <=  1'b0;
	       cache_inhibit <=  1'b0;
	    end	  
	  `OR1200_ICFSM_CFETCH: begin	// fetch
	     
	     if (icqmem_cycstb_i & icqmem_ci_i)
	       cache_inhibit <=  1'b1;
	     
	     if (hitmiss_eval)
	       saved_addr_r[31:`OR1200_ICTAGL] <= start_addr[31:`OR1200_ICTAGL];

	     // Check for stopped cache loads
	         // instruction cache turned-off
	     if ((!ic_en) ||
		 // fetch aborted (usually caused by IMMU)
		 (hitmiss_eval & !icqmem_cycstb_i) ||	
		 (biudata_error) ||  // fetch terminated with an error
		 // fetch from cache-inhibited page
		 (cache_inhibit & biudata_valid)) begin	
		state <=  `OR1200_ICFSM_IDLE;
		hitmiss_eval <=  1'b0;
		load <=  1'b0;
		cache_inhibit <=  1'b0;
	     end // if ((!ic_en) ||...	     
	     // fetch missed, wait for first fetch and continue filling line
	     else if (tagcomp_miss & biudata_valid) begin	
		state <=  `OR1200_ICFSM_LREFILL3;
		saved_addr_r[`OR1200_ICLS-1:2] 
		  <= saved_addr_r[`OR1200_ICLS-1:2] + 1;
		hitmiss_eval <=  1'b0;
		cnt <= ((1 << `OR1200_ICLS) - (2 * 4));
		cache_inhibit <=  1'b0;
	     end
	     // fetch aborted (usually caused by exception)
	     else if (!icqmem_cycstb_i
		      & !last_eval_miss // JPB
		      ) begin	
		state <=  `OR1200_ICFSM_IDLE;
		hitmiss_eval <=  1'b0;
		load <=  1'b0;
		cache_inhibit <=  1'b0;
	     end
	     // fetch hit, wait in this state for now
	     else if (!tagcomp_miss & !icqmem_ci_i) begin
		saved_addr_r <=  start_addr;
		cache_inhibit <=  1'b0;
	     end
	     else   // fetch in-progress
	       hitmiss_eval <=  1'b0;

	     if (hitmiss_eval & !tagcomp_miss) // JPB
	       last_eval_miss <= 1; // JPB
	     
	  end
	  `OR1200_ICFSM_LREFILL3 : begin
	     // abort because IC has just been turned off
             if (!ic_en) begin
		// invalidate before IC can be turned on
		state <=  `OR1200_ICFSM_IDLE;	
                saved_addr_r <=  start_addr;
                hitmiss_eval <=  1'b0;
                load <=  1'b0;
             end
	     // refill ack, more fetchs to come
	     else if (biudata_valid && (|cnt)) begin	
		cnt <=  cnt - `OR1200_ICLS'd4;
		saved_addr_r[`OR1200_ICLS-1:2] 
		  <= saved_addr_r[`OR1200_ICLS-1:2] + 1;
	     end
	     // last fetch of line refill
	     else if (biudata_valid) begin
		state <=  `OR1200_ICFSM_IDLE;
		saved_addr_r <=  start_addr;
		hitmiss_eval <=  1'b0;
		load <=  1'b0;
	     end
	  end
	  default:
	    state <=  `OR1200_ICFSM_IDLE;
	endcase
   end

endmodule
