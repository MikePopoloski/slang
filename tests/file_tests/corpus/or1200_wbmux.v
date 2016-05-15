//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Write-back Mux                                     ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  CPU's write-back stage of the pipeline                      ////
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
//
// $Log: or1200_wbmux.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_wbmux(
	// Clock and reset
	clk, rst,

	// Internal i/f
	wb_freeze, rfwb_op,
	muxin_a, muxin_b, muxin_c, muxin_d, muxin_e,
	muxout, muxreg, muxreg_valid
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
// Internal i/f
//
input				wb_freeze;
input	[`OR1200_RFWBOP_WIDTH-1:0]	rfwb_op;
input	[width-1:0]		muxin_a;
input	[width-1:0]		muxin_b;
input	[width-1:0]		muxin_c;
input	[width-1:0]		muxin_d;
input	[width-1:0]		muxin_e;   
output	[width-1:0]		muxout;
output	[width-1:0]		muxreg;
output				muxreg_valid;

//
// Internal wires and regs
//
reg	[width-1:0]		muxout;
reg	[width-1:0]		muxreg;
reg				muxreg_valid;

//
// Registered output from the write-back multiplexer
//
always @(posedge clk or `OR1200_RST_EVENT rst) begin
	if (rst == `OR1200_RST_VALUE) begin
		muxreg <=  32'd0;
		muxreg_valid <=  1'b0;
	end
	else if (!wb_freeze) begin
		muxreg <=  muxout;
		muxreg_valid <=  rfwb_op[0];
	end
end

//
// Write-back multiplexer
//
always @(muxin_a or muxin_b or muxin_c or muxin_d or muxin_e or rfwb_op) begin
`ifdef OR1200_ADDITIONAL_SYNOPSYS_DIRECTIVES
	casez(rfwb_op[`OR1200_RFWBOP_WIDTH-1:1]) // synopsys parallel_case infer_mux
`else
	casez(rfwb_op[`OR1200_RFWBOP_WIDTH-1:1]) // synopsys parallel_case
`endif
		`OR1200_RFWBOP_ALU: muxout = muxin_a;
		`OR1200_RFWBOP_LSU: begin
			muxout = muxin_b;
`ifdef OR1200_VERBOSE
// synopsys translate_off
			$display("  WBMUX: muxin_b %h", muxin_b);
// synopsys translate_on
`endif
		end
		`OR1200_RFWBOP_SPRS: begin
			muxout = muxin_c;
`ifdef OR1200_VERBOSE
// synopsys translate_off
			$display("  WBMUX: muxin_c %h", muxin_c);
// synopsys translate_on
`endif
		end
		`OR1200_RFWBOP_LR: begin
			muxout = muxin_d + 32'h8;
`ifdef OR1200_VERBOSE
// synopsys translate_off
			$display("  WBMUX: muxin_d %h", muxin_d + 4'h8);
// synopsys translate_on
`endif
		end
`ifdef OR1200_FPU_IMPLEMENTED
	        `OR1200_RFWBOP_FPU : begin
	     muxout = muxin_e;	     
 `ifdef OR1200_VERBOSE
// synopsys translate_off
			$display("  WBMUX: muxin_e %h", muxin_e);
// synopsys translate_on
`endif
	       end		      
`endif
	  default : begin
	     muxout = 0;
	  end
	  
	endcase
end

endmodule
