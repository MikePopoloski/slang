//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Generic 32x32 multiplier                                    ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  Generic 32x32 multiplier with pipeline stages.              ////
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
// CVS Revision History
//
// $Log: or1200_gmultp2_32x32.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

// 32x32 multiplier, no input/output registers
// Registers inside Wallace trees every 8 full adder levels,
// with first pipeline after level 4

`ifdef OR1200_GENERIC_MULTP2_32X32

`define OR1200_W 32
`define OR1200_WW 64

module or1200_gmultp2_32x32 ( X, Y, CLK, RST, P );

input   [`OR1200_W-1:0]  X;
input   [`OR1200_W-1:0]  Y;
input           CLK;
input           RST;
output  [`OR1200_WW-1:0]  P;

reg     [`OR1200_W-1:0]  X_saved;
reg     [`OR1200_W-1:0]  Y_saved;
reg     [`OR1200_WW-1:0]  p1;
integer 		  xi;
integer 		  yi;

//
// Conversion unsigned to signed
//
always @(X_saved)
	xi = X_saved;

//
// Conversion unsigned to signed
//
always @(Y_saved)
	yi = Y_saved;

//
// First multiply stage
//
always @(posedge CLK or `OR1200_RST_EVENT RST)
        if (RST == `OR1200_RST_VALUE) begin
           X_saved <= `OR1200_W'b0;
	   Y_saved <= `OR1200_W'b0;
	end
        else begin
           X_saved <= X;
	   Y_saved <= Y;
	end

//
// Second multiply stage
//
always @(posedge CLK or `OR1200_RST_EVENT RST)
        if (RST == `OR1200_RST_VALUE)
          p1 <= `OR1200_WW'b0;
        else
          p1 <=  xi * yi;

assign P = p1;

endmodule

`endif
