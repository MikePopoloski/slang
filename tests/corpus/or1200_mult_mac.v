//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Top level multiplier, divider and MAC              ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Multiplier is 32x32 however multiply instructions only      ////
////  use lower 32 bits of the result. MAC is 32x32=64+64.        ////
////                                                              ////
////  To Do:                                                      ////
////   - make signed division better, w/o negating the operands   ////
////   - implement non-serial divider that is synthesizable       ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////      - Julius Baxter, julius@opencores.org                   ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000, 2010 Authors and OPENCORES.ORG           ////
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
// $Log: or1200_mult_mac.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Bugs fixed. 
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_mult_mac(
		       // Clock and reset
		       clk, rst,

		       // Multiplier/MAC interface
		       ex_freeze, id_macrc_op, macrc_op, a, b, mac_op, alu_op, 
		       result, mult_mac_stall,

		       // Overflow
		       ovforw, ov_we,
		       
		       // SPR interface
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
   // Multiplier/MAC interface
   //
   input				ex_freeze;
   input				id_macrc_op;
   input				macrc_op;
   input [width-1:0] 			a;
   input [width-1:0] 			b;
   input [`OR1200_MACOP_WIDTH-1:0] 	mac_op;
   input [`OR1200_ALUOP_WIDTH-1:0] 	alu_op;
   output [width-1:0] 			result;
   output				mult_mac_stall;
   output 				ovforw, ov_we;
   
   //
   // SPR interface
   //
   input				spr_cs;
   input				spr_write;
   input [31:0] 			spr_addr;
   input [31:0] 			spr_dat_i;
   output [31:0] 			spr_dat_o;

   //
   // Internal wires and regs
   //
   reg [width-1:0] 			result;
   reg 					ex_freeze_r;
   wire 				alu_op_mul;
   wire 				alu_op_smul;      
`ifdef OR1200_MULT_IMPLEMENTED
   reg [2*width-1:0] 			mul_prod_r;
   wire 				alu_op_umul;   
 `ifdef OR1200_MULT_SERIAL
   reg [5:0] 				serial_mul_cnt;   
   reg 					mul_free;   
 `endif
`else
   wire [2*width-1:0] 			mul_prod_r;
`endif
   wire [2*width-1:0] 			mul_prod;
   wire 				mul_stall;
   reg [1:0] 				mul_stall_count;   
   wire [`OR1200_MACOP_WIDTH-1:0] 	mac_op;
`ifdef OR1200_MAC_IMPLEMENTED
   reg [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r1;
   reg [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r2;
   reg [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r3;
   reg 					mac_stall_r;
   reg [63:0] 				mac_r;
`else
   wire [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r1;
   wire [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r2;
   wire [`OR1200_MACOP_WIDTH-1:0] 	mac_op_r3;
   wire 				mac_stall_r;
   wire [63:0] 				mac_r;
`endif
   wire [width-1:0] 			x;
   wire [width-1:0] 			y;
   wire 				spr_maclo_we;
   wire 				spr_machi_we; 
   wire 				alu_op_div;  
   wire 				alu_op_udiv;
   wire 				alu_op_sdiv;
   reg 					div_free;
   wire 			        div_stall;
`ifdef OR1200_DIV_IMPLEMENTED
 `ifdef OR1200_DIV_SERIAL
   reg [2*width-1:0] 			div_quot_r;   
   wire [width-1:0] 			div_tmp;
   reg [5:0] 				div_cntr;
 `else
   reg [width-1:0] 			div_quot_r;      
   reg [width-1:0] 			div_quot_generic;   
 `endif
   wire 				div_by_zero;
`endif
   reg 					ovforw, ov_we;
   
   //
   // Combinatorial logic
   //
`ifdef OR1200_MULT_IMPLEMENTED
   assign alu_op_smul = (alu_op == `OR1200_ALUOP_MUL);
   assign alu_op_umul = (alu_op == `OR1200_ALUOP_MULU);
   assign alu_op_mul = alu_op_smul | alu_op_umul;
`else
   assign alu_op_smul = 0;
   assign alu_op_mul = 0;
`endif
`ifdef OR1200_MAC_IMPLEMENTED
   assign spr_maclo_we = spr_cs & spr_write & spr_addr[`OR1200_MAC_ADDR];
   assign spr_machi_we = spr_cs & spr_write & !spr_addr[`OR1200_MAC_ADDR];
   assign spr_dat_o = spr_addr[`OR1200_MAC_ADDR] ? mac_r[31:0] : mac_r[63:32];
`else
   assign spr_maclo_we = 1'b0;
   assign spr_machi_we = 1'b0;
   assign spr_dat_o = 32'h0000_0000;
`endif
`ifdef OR1200_DIV_IMPLEMENTED
   assign alu_op_sdiv = (alu_op == `OR1200_ALUOP_DIV);
   assign alu_op_udiv = (alu_op == `OR1200_ALUOP_DIVU);
   assign alu_op_div = alu_op_sdiv | alu_op_udiv;   
`else
   assign alu_op_udiv = 1'b0;
   assign alu_op_sdiv = 1'b0;
   assign alu_op_div = 1'b0;   
`endif

   assign x = (alu_op_sdiv | alu_op_smul) & a[31] ? ~a + 32'b1 : 
	      alu_op_div | alu_op_mul | (|mac_op) ? a : 32'd0;
   assign y = (alu_op_sdiv | alu_op_smul) & b[31] ? ~b + 32'b1 : 
	      alu_op_div | alu_op_mul | (|mac_op) ? b : 32'd0;

   assign div_by_zero = !(|b) & alu_op_div;
   

   // Used to indicate when we should check for new multiply or MAC ops
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       ex_freeze_r <= 1'b1;
     else
       ex_freeze_r <= ex_freeze;

   //
   // Select result of current ALU operation to be forwarded
   // to next instruction and to WB stage
   //
   always @*
     casez(alu_op)	// synopsys parallel_case
`ifdef OR1200_DIV_IMPLEMENTED
       `OR1200_ALUOP_DIV: begin
	  result = a[31] ^ b[31] ? ~div_quot_r[31:0] + 32'd1 : div_quot_r[31:0];
       end
       `OR1200_ALUOP_DIVU: begin
	  result = div_quot_r[31:0];
       end
`endif
`ifdef OR1200_MULT_IMPLEMENTED    
       `OR1200_ALUOP_MUL: begin
	  result = a[31] ^ b[31] ? ~mul_prod_r[31:0] + 32'd1 : mul_prod_r[31:0];
       end
	 `OR1200_ALUOP_MULU: begin
	  result = mul_prod_r[31:0];
       end
`endif    
       default:
`ifdef OR1200_MAC_IMPLEMENTED      
 `ifdef OR1200_MAC_SHIFTBY
	 result = mac_r[`OR1200_MAC_SHIFTBY+31:`OR1200_MAC_SHIFTBY];
 `else
       result = mac_r[31:0];
 `endif
`else
       result = {width{1'b0}};    
`endif    
     endcase // casez (alu_op)


   //
   // Overflow generation
   //
   always @*
     casez(alu_op)	// synopsys parallel_case
`ifdef OR1200_IMPL_OV       
 `ifdef OR1200_MULT_IMPLEMENTED
       `OR1200_ALUOP_MUL: begin
	  // Actually doing unsigned multiply internally, and then negate on
	  // output as appropriate, so if sign bit is set, then is overflow
          // unless incoming signs differ and result is 2^(width-1)
          ovforw = (mul_prod_r[width-1] && 
                    !((a[width-1]^b[width-1]) && ~|mul_prod_r[width-2:0])) ||
                   |mul_prod_r[2*width-1:32];

	  ov_we = 1;
       end
       `OR1200_ALUOP_MULU : begin
	  // Overflow on unsigned multiply is simpler.
	  ovforw = |mul_prod_r[2*width-1:32];
	  ov_we = 1;
       end
 `endif //  `ifdef OR1200_MULT_IMPLEMENTED
 `ifdef OR1200_DIV_IMPLEMENTED
       `OR1200_ALUOP_DIVU,
       `OR1200_ALUOP_DIV: begin
	  // Overflow on divide by zero or -2^(width-1)/-1
	  ovforw = div_by_zero || (a==32'h8000_0000 && b==32'hffff_ffff);
	  ov_we = 1;
       end
 `endif
`endif //  `ifdef OR1200_IMPL_OV
       default: begin
	  ovforw = 0;
	  ov_we = 0;
       end
     endcase // casez (alu_op)
   

`ifdef OR1200_MULT_IMPLEMENTED
 `ifdef OR1200_MULT_SERIAL

   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE) begin
	mul_prod_r <=  64'h0000_0000_0000_0000;
	serial_mul_cnt <= 6'd0;
	mul_free <= 1'b1;
	
     end
     else if (|serial_mul_cnt) begin
	serial_mul_cnt <= serial_mul_cnt - 6'd1;
	if (mul_prod_r[0])
	  mul_prod_r[(width*2)-1:width-1] <= mul_prod_r[(width*2)-1:width] + x;
	else
	  mul_prod_r[(width*2)-1:width-1] <= {1'b0,mul_prod_r[(width*2)-1:
							      width]};
	mul_prod_r[width-2:0] <= mul_prod_r[width-1:1];
	
     end
     else if (alu_op_mul && mul_free) begin
	mul_prod_r <= {32'd0, y};
	mul_free <= 0;
	serial_mul_cnt <= 6'b10_0000;
     end
     else if (!ex_freeze | mul_free) begin
	mul_free <= 1'b1;	
     end

   assign mul_stall = (|serial_mul_cnt) | (alu_op_mul & !ex_freeze_r);
   
 `else
   
   //
   // Instantiation of the multiplier
   //
  `ifdef OR1200_ASIC_MULTP2_32X32
   or1200_amultp2_32x32 or1200_amultp2_32x32(
					     .X(x),
					     .Y(y),
					     .RST(rst),
					     .CLK(clk),
					     .P(mul_prod)
					     );
  `else // OR1200_ASIC_MULTP2_32X32
   or1200_gmultp2_32x32 or1200_gmultp2_32x32(
					     .X(x),
					     .Y(y),
					     .RST(rst),
					     .CLK(clk),
					     .P(mul_prod)
					     );
  `endif // OR1200_ASIC_MULTP2_32X32   
   
   //
   // Registered output from the multiplier
   //
   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE) begin
	mul_prod_r <=  64'h0000_0000_0000_0000;
     end
     else begin
	mul_prod_r <=  mul_prod[63:0];
     end

   //
   // Generate stall signal during multiplication
   //
   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE)
       mul_stall_count <= 0;
     else if (!(|mul_stall_count))
       mul_stall_count <= {mul_stall_count[0], alu_op_mul & !ex_freeze_r};
     else 
       mul_stall_count <= {mul_stall_count[0],1'b0};
       
   assign mul_stall = (|mul_stall_count) | 
		      (!(|mul_stall_count) & alu_op_mul & !ex_freeze_r);
   
 `endif // !`ifdef OR1200_MULT_SERIAL   
   
`else // OR1200_MULT_IMPLEMENTED
   assign mul_prod = {2*width{1'b0}};
   assign mul_prod_r = {2*width{1'b0}};
   assign mul_stall = 0;   
`endif // OR1200_MULT_IMPLEMENTED

`ifdef OR1200_MAC_IMPLEMENTED
   
   //
   // Propagation of l.mac opcode, only register it for one cycle
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       mac_op_r1 <=  `OR1200_MACOP_WIDTH'b0;
     else
       mac_op_r1 <=  !ex_freeze_r ? mac_op : `OR1200_MACOP_WIDTH'b0;

   //
   // Propagation of l.mac opcode
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       mac_op_r2 <=  `OR1200_MACOP_WIDTH'b0;
     else
       mac_op_r2 <=  mac_op_r1;

   //
   // Propagation of l.mac opcode
   //
   always @(posedge clk or `OR1200_RST_EVENT rst)
     if (rst == `OR1200_RST_VALUE)
       mac_op_r3 <=  `OR1200_MACOP_WIDTH'b0;
     else
       mac_op_r3 <=  mac_op_r2;

   //
   // Implementation of MAC
   //
   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE)
       mac_r <=  64'h0000_0000_0000_0000;
 `ifdef OR1200_MAC_SPR_WE
     else if (spr_maclo_we)
       mac_r[31:0] <=  spr_dat_i;
     else if (spr_machi_we)
       mac_r[63:32] <=  spr_dat_i;
 `endif
     else if (mac_op_r3 == `OR1200_MACOP_MAC)
       mac_r <=  mac_r + mul_prod_r;
     else if (mac_op_r3 == `OR1200_MACOP_MSB)
       mac_r <=  mac_r - mul_prod_r;
     else if (macrc_op && !ex_freeze)
       mac_r <=  64'h0000_0000_0000_0000;

   //
   // Stall CPU if l.macrc is in ID and MAC still has to process l.mac 
   // instructions in EX stage (e.g. inside multiplier)
   // This stall signal is also used by the divider.
   //
   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE)
       mac_stall_r <=  1'b0;
     else
       mac_stall_r <=  (|mac_op | (|mac_op_r1) | (|mac_op_r2)) & 
		       (id_macrc_op | mac_stall_r);
   
`else // OR1200_MAC_IMPLEMENTED
   assign mac_stall_r = 1'b0;
   assign mac_r = {2*width{1'b0}};
   assign mac_op_r1 = `OR1200_MACOP_WIDTH'b0;
   assign mac_op_r2 = `OR1200_MACOP_WIDTH'b0;
   assign mac_op_r3 = `OR1200_MACOP_WIDTH'b0;
`endif // OR1200_MAC_IMPLEMENTED

`ifdef OR1200_DIV_IMPLEMENTED   
   
   //
   // Serial division
   //
 `ifdef OR1200_DIV_SERIAL
   assign div_tmp = div_quot_r[63:32] - y;   
   always @(`OR1200_RST_EVENT rst or posedge clk)
     if (rst == `OR1200_RST_VALUE) begin
	div_quot_r <=  64'h0000_0000_0000_0000;
	div_free <=  1'b1;
	div_cntr <=  6'b00_0000;
     end
     else if (div_by_zero) begin
	div_quot_r <=  64'h0000_0000_0000_0000;
	div_free <=  1'b1;
	div_cntr <=  6'b00_0000;
     end
     else if (|div_cntr) begin
	if (div_tmp[31])
	  div_quot_r <=  {div_quot_r[62:0], 1'b0};
	else
	  div_quot_r <=  {div_tmp[30:0], div_quot_r[31:0], 1'b1};
	div_cntr <=  div_cntr - 6'd1;
     end
     else if (alu_op_div && div_free) begin
	div_quot_r <=  {31'b0, x[31:0], 1'b0};
	div_cntr <=  6'b10_0000;
	div_free <=  1'b0;
     end
     else if (div_free | !ex_freeze) begin
	div_free <=  1'b1;
     end

   assign div_stall = (|div_cntr) | (!ex_freeze_r & alu_op_div);


 `else // !`ifdef OR1200_DIV_SERIAL

   // Full divider
   // TODO: Perhaps provide module that can be technology dependent.
   always @(`OR1200_RST_EVENT rst or posedge clk) begin     
      if (rst == `OR1200_RST_VALUE) begin
	 div_quot_r <=  32'd0;	   
	 div_quot_generic <= 32'd0;	   
      end
      else begin
	 if (alu_op_udiv & !(|y)) // unsigned divide by 0 - force to MAX
	   div_quot_generic[31:0] <= 32'hffff_ffff;	   
	 else if (alu_op_div)
	   div_quot_generic[31:0] <= x / y;
      end

      // Add any additional statges of pipelining as required here. Ensure
      // ends with div_quot_r.
      // Then add logic to ensure div_stall stays high for as long as the
      // division should take.      
      
      div_quot_r[31:0] <= div_quot_generic;

   end     
   
   assign div_stall = 0;
   
 `endif   

`else // !`ifdef OR1200_DIV_IMPLEMENTED

   assign div_stall = 0;

`endif // !`ifdef OR1200_DIV_IMPLEMENTED
   
   
   //   
   // Stall output
   //
   assign mult_mac_stall = mac_stall_r | div_stall | mul_stall;
   
endmodule
