//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's FPU Wrapper                                        ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Wrapper for floating point unit.                            ////
////  Interface based on MULT/MAC unit.                           ////
////                                                              ////
////  To Do:                                                      ////
////   - lf.rem.s and lf.madd.s instruction support               ////
////   - implement FP SPRs as needed                              ////
////                                                              ////
////  Author(s):                                                  ////
////      - Julius Baxter, julius@opencores.org                   ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2009,2010 Authors and OPENCORES.ORG            ////
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

module or1200_fpu(
		  // Clock and reset
		  clk, rst,

		  // FPU interface
		  ex_freeze, a, b, fpu_op, result, done,

		  // Flag controls
		  flagforw, flag_we,

		  // Exception signal
		  sig_fp, except_started,

		  // FPCSR system register
		  fpcsr_we, fpcsr,
		  
		  // SPR interface -- currently unused
		  spr_cs, spr_write, spr_addr, spr_dat_i, spr_dat_o
		  );

   parameter width = `OR1200_OPERAND_WIDTH;

   //
   // I/O
   //

   //
   // Clock and reset
   //
   input				clk;
   input				rst;

   //
   // FPU interface
   //
   input				ex_freeze;
   input [width-1:0] 			a;
   input [width-1:0] 			b;
   input [`OR1200_FPUOP_WIDTH-1:0] 	fpu_op;
   output [width-1:0] 			result;
   output 				done;
   
   //
   // Flag signals
   //
   output 				flagforw;
   output 				flag_we;

   //
   // FPCSR interface
   //  
   input 				fpcsr_we;   
   output [`OR1200_FPCSR_WIDTH-1:0] 	fpcsr;   

   //
   // Exception signal
   //   
   output 				sig_fp;
   input 				except_started;
   
   
   //
   // SPR interface
   //
   input				spr_cs;
   input				spr_write;
   input [31:0] 			spr_addr;
   input [31:0] 			spr_dat_i;
   output [31:0] 			spr_dat_o;


`ifndef OR1200_FPU_IMPLEMENTED
   
   // No FPU needed
   assign result = 0;
   assign flagforw  = 0;
   assign flag_we = 0;
   assign sig_fp = 0;
   assign spr_dat_o = 0;
   assign fpcsr = 0;
   assign done = 1;   
`else

   
   //
   // Internals
   //
   wire 				fpu_op_is_arith, fpu_op_is_conv, 
					fpu_op_is_comp;
   wire 				fpu_op_r_is_arith, fpu_op_r_is_conv, 
					fpu_op_r_is_comp;
   wire 				fpu_arith_done, fpu_conv_done, 
					fpu_comp_done;
   wire [width-1:0] 			result_arith, result_conv;
   
   reg [`OR1200_FPUOP_WIDTH-1:0] 	fpu_op_r;   
   reg [`OR1200_FPCSR_WIDTH-1:0] 	fpcsr_r;
   wire 				fpu_op_valid;
   reg 					fpu_op_valid_re;   
   wire 				fpu_check_op;   
   wire 				inf, inv_inf_op_in,snan, snan_in,qnan, 
					ine, overflow, underflow, zero, dbz, 
					dbz_in, mul_z_inf, nan_in;
   wire 				altb, blta, aeqb, inf_cmp, zero_cmp, 
					unordered ;
   wire 				snan_conv, ine_conv, inv_conv, 
					zero_conv, underflow_conv, 
					overflow_conv;
   wire 				inv_comp;   
   reg 					flag;

   
   assign spr_dat_o = 0;
   
   assign fpcsr = fpcsr_r;
   
   assign sig_fp = fpcsr_r[`OR1200_FPCSR_FPEE] 
	    & (|fpcsr_r[`OR1200_FPCSR_WIDTH-1:`OR1200_FPCSR_OVF]);

   // Top bit indicates FPU instruction
   assign fpu_op_valid = fpu_op[`OR1200_FPUOP_WIDTH-1];

   assign fpu_check_op = !ex_freeze & fpu_op_valid;   
      
   // Generate signals to latch fpu_op from decode instruction, then latch 
   // operands when they appear during execute stage
   
   assign fpu_op_is_arith = !(|fpu_op[3:2]);
   assign fpu_op_is_conv = fpu_op[2] & !fpu_op[3];   
   assign fpu_op_is_comp = fpu_op[3];

   assign fpu_op_r_is_arith = !(|fpu_op_r[3:2]);
   assign fpu_op_r_is_conv = fpu_op_r[2] & !fpu_op_r[3];   
   assign fpu_op_r_is_comp = fpu_op_r[3];

   assign done = (fpu_op_r_is_arith & fpu_arith_done) |
		 (fpu_op_r_is_conv & fpu_conv_done)   |
		 (fpu_op_r_is_comp & fpu_comp_done)   ;
   
   // Register fpu_op (remove FPU op valid bit [7], replace with 0)
   always @(posedge clk)
     if (fpu_check_op)
       fpu_op_r <= {1'b0,fpu_op[`OR1200_FPUOP_WIDTH-2:0]}; 

   // Indicate new FPU op
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE) 
       fpu_op_valid_re <= 0;
     else if (fpu_op_valid_re)
       fpu_op_valid_re <= 0;
     else if (fpu_check_op)
       fpu_op_valid_re <= 1;   
   
   //
   // FPCSR system group register implementation
   //   
   always @(posedge clk or `OR1200_RST_EVENT rst) begin
      if (rst == `OR1200_RST_VALUE)
	fpcsr_r <= 0;
      else
	begin
	   if (fpcsr_we)
	     fpcsr_r <= b[`OR1200_FPCSR_WIDTH-1:0];
           else if (done)
	     begin
		fpcsr_r[`OR1200_FPCSR_OVF] <= (overflow & fpu_op_r_is_arith);
		fpcsr_r[`OR1200_FPCSR_UNF] <= (underflow & fpu_op_r_is_arith) |
					  (underflow_conv  & fpu_op_r_is_conv);
		fpcsr_r[`OR1200_FPCSR_SNF] <= (snan  & fpu_op_r_is_arith)|
					      (snan_conv & fpu_op_r_is_conv);
		fpcsr_r[`OR1200_FPCSR_QNF] <= (qnan  & fpu_op_r_is_arith);
		fpcsr_r[`OR1200_FPCSR_ZF]  <= (zero  & fpu_op_r_is_arith) | 
					      (zero_cmp & fpu_op_r_is_comp) |
					      (zero_conv & fpu_op_r_is_conv);
		fpcsr_r[`OR1200_FPCSR_IXF] <= (ine  & fpu_op_r_is_arith) |
					      (ine_conv & fpu_op_r_is_conv);
		fpcsr_r[`OR1200_FPCSR_IVF] <= 
				((snan_in | dbz_in | inv_inf_op_in | mul_z_inf) & 
					   fpu_op_r_is_arith) |
				  ((inv_conv | snan_conv) & fpu_op_r_is_conv) |
					      (inv_comp & fpu_op_r_is_comp);
		fpcsr_r[`OR1200_FPCSR_INF] <= (inf  & fpu_op_r_is_arith) | 
					      (inf_cmp & fpu_op_r_is_comp);
		fpcsr_r[`OR1200_FPCSR_DZF] <= (dbz & fpu_op_r_is_arith);
	     end // if (fpu_arith_done | fpu_conv_done)	   
	   if (except_started)
	     fpcsr_r[`OR1200_FPCSR_FPEE] <= 0;
	end // else: !if(rst)
   end // always @ (posedge clk or `OR1200_RST_EVENT rst)

   //
   // Comparison flag generation
   //
   always @*
     begin
	// Get rid of top bit - is FPU op valid bit
	case({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]})
	  `OR1200_FPCOP_SFEQ: begin
	     flag = aeqb;
	  end
	  `OR1200_FPCOP_SFNE: begin
	     flag = !aeqb;
	       end
	  `OR1200_FPCOP_SFGT: begin
	     flag = blta & !aeqb;
	  end
	  `OR1200_FPCOP_SFGE: begin
	     flag = blta | aeqb;
	  end
	  `OR1200_FPCOP_SFLT: begin
	     flag = altb & !aeqb;
	  end
	  `OR1200_FPCOP_SFLE: begin
	     flag = altb | aeqb;
	  end
	  default: begin
	     flag = 0;
	  end
	endcase // case (fpu_op_r)
     end // always@ (posedge clk)
   
   assign flagforw = flag;
   
   // Determine here where we do the write, ie how much we pipeline the 
   // comparison
   assign flag_we = fpu_op_r_is_comp & fpu_comp_done;

   // MUX for outputs from arith and conversion modules
   assign result = fpu_op_r_is_conv ? result_conv : result_arith;   

   //
   // Instantiate FPU modules
   //
   
   // FPU 100 VHDL core from OpenCores.org: http://opencores.org/project,fpu100
   // Used only for add,sub,mul,div
   or1200_fpu_arith fpu_arith
     (
      .clk_i(clk),
      .opa_i(a),
      .opb_i(b),
      .fpu_op_i({1'b0,fpu_op_r[1:0]}), // Only bottom 2 bits
      .rmode_i(fpcsr_r[`OR1200_FPCSR_RM]),
      .output_o(result_arith),
      .start_i(fpu_op_valid_re & fpu_op_r_is_arith),
      .ready_o(fpu_arith_done),
      .ine_o(ine),
      .overflow_o(overflow),
      .underflow_o(underflow),
      .div_zero_o(dbz),
      .inf_o(inf),
      .zero_o(zero),
      .qnan_o(qnan),
      .snan_o(snan)
      );

   // Logic for detection of signaling NaN on input
   // signaling NaN: exponent is 8hff, [22] is zero, rest of fract is non-zero
   // quiet NaN: exponent is 8hff, [22] is 1
   reg a_is_snan, b_is_snan;
   reg a_is_qnan, b_is_qnan;
   
   always @(posedge clk)
     begin
	a_is_snan <= (a[30:23]==8'hff) & !a[22] & (|a[21:0]);
	b_is_snan <= (b[30:23]==8'hff) & !b[22] & (|b[21:0]);
	a_is_qnan <= (a[30:23]==8'hff) & a[22];
	b_is_qnan <= (b[30:23]==8'hff) & b[22];	
     end
   // Signal to indicate there was a signaling NaN on input
   assign snan_in = a_is_snan | b_is_snan;

   // Check for, add with opposite signed infinities, or subtract with 
   // same signed infinities.
   reg a_is_inf, b_is_inf, a_b_sign_xor;
   
   always @(posedge clk)
     begin
	a_is_inf <= (a[30:23]==8'hff) & !(|a[22:0]);
	b_is_inf <= (b[30:23]==8'hff) & !(|a[22:0]);
	a_b_sign_xor <= a[31] ^ b[31];
     end
   
   assign inv_inf_op_in = (a_is_inf & b_is_inf) & 
			  ((a_b_sign_xor & 
			    ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} == 
			     `OR1200_FPUOP_ADD)) |
			   (!a_b_sign_xor & 
			    ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} == 
			     `OR1200_FPUOP_SUB))) ;
   
   // Check if it's 0.0/0.0 to generate invalid signal (ignore sign bit)
   reg a_is_zero, b_is_zero;
   
   always @(posedge clk)
     begin
	a_is_zero <= !(|a[30:0]);
	b_is_zero <= !(|b[30:0]);
     end
   assign dbz_in = ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} == 
		    `OR1200_FPUOP_DIV) & (a_is_zero & b_is_zero);
   
   
   assign mul_z_inf = ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} == 
		       `OR1200_FPUOP_MUL) & 
		      ((a_is_zero & b_is_inf) | (b_is_zero & a_is_inf));
   
   assign nan_in = (a_is_snan | b_is_snan | a_is_qnan | b_is_qnan);

   // 32-bit integer <-> single precision floating point conversion unit
   or1200_fpu_intfloat_conv fpu_intfloat_conv
     ( 
       .clk(clk),
       .rmode(fpcsr_r[`OR1200_FPCSR_RM]),
       .fpu_op(fpu_op_r[2:0]),
       .opa(a),
       .out(result_conv),
       .snan(snan_conv),
       .ine(ine_conv),
       .inv(inv_conv),
       .overflow(overflow_conv),
       .underflow(underflow_conv),
       .zero(zero_conv)
       );

   // 5-long shift reg for conversion ready counter
   reg [6:0] fpu_conv_shr;
   always @(posedge clk)
     fpu_conv_shr <= {fpu_conv_shr[5:0],fpu_check_op & fpu_op_is_conv};
   assign fpu_conv_done = fpu_conv_shr[6];

   // Single precision floating point number comparison module
   or1200_fpu_fcmp fpu_fcmp
     (
      .opa(a), 
      .opb(b), 
      .unordered(unordered),
      // I am convinced the comparison logic is wrong way around in this 
      // module, simplest to swap them on output -- julius       
      .altb(blta), 
      .blta(altb), 
      .aeqb(aeqb), 
      .inf(inf_cmp), 
      .zero(zero_cmp));

   reg 	     fpu_op_valid_re_r;
   always @(posedge clk)
     fpu_op_valid_re_r  <= fpu_op_valid_re;
   
   assign fpu_comp_done = fpu_op_valid_re_r & fpu_op_r_is_comp;

   // Comparison invalid when sNaN in on an equal comparison, or any NaN 
   // for any other comparison.
   assign inv_comp =  (snan_in & ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} 
				  == `OR1200_FPCOP_SFEQ)) | 
		      (nan_in & ({1'b0,fpu_op_r[`OR1200_FPUOP_WIDTH-2:0]} 
				 != `OR1200_FPCOP_SFEQ));
   
`endif // !`ifndef OR1200_FPU_IMPLEMENTED
   
endmodule // or1200_fpu
