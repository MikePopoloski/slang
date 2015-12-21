//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Xilinx Virtex RAM 32x8D                                     ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  Virtex dual-port memory                                     ////
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
// $Log: or1200_xcv_ram32x8d.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// No update 
//
// Revision 1.2  2002/07/14 22:17:17  lampret
// Added simple trace buffer [only for Xilinx Virtex target]. Fixed instruction fetch abort when new exception is recognized.
//
// Revision 1.1  2002/01/03 08:16:15  lampret
// New prefixes for RTL files, prefixed module names. Updated cache controllers and MMUs.
//
// Revision 1.7  2001/10/21 17:57:16  lampret
// Removed params from generic_XX.v. Added translate_off/on in sprs.v and id.v. Removed spr_addr from dc.v and ic.v. Fixed CR+LF.
//
// Revision 1.6  2001/10/14 13:12:10  lampret
// MP3 version.
//
// Revision 1.1.1.1  2001/10/06 10:18:36  igorm
// no message
//
// Revision 1.1  2001/08/09 13:39:33  lampret
// Major clean-up.
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

`ifdef OR1200_XILINX_RAM32X1D
`ifdef OR1200_USE_RAM16X1D_FOR_RAM32X1D
module or1200_xcv_ram32x8d
(
    DPO,
    SPO,
    A,
    D,
    DPRA,
    WCLK,
    WE
);
output  [7:0]   DPO;
output  [7:0]   SPO;
input   [4:0]   A;
input   [4:0]   DPRA;
input   [7:0]   D;
input           WCLK;
input           WE;

wire    [7:0]   DPO_0;
wire    [7:0]   SPO_0;

wire    [7:0]   DPO_1;
wire    [7:0]   SPO_1;

wire            WE_0 ;
wire            WE_1 ;

assign DPO = DPRA[4] ? DPO_1 : DPO_0 ;
assign SPO = A[4] ? SPO_1 : SPO_0 ;

assign WE_0 = !A[4] && WE ;
assign WE_1 =  A[4] && WE ;

RAM16X1D ram32x1d_0_0(
	.DPO(DPO_0[0]),
	.SPO(SPO_0[0]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[0]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 1
//
RAM16X1D ram32x1d_0_1(
	.DPO(DPO_0[1]),
	.SPO(SPO_0[1]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[1]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 2
//
RAM16X1D ram32x1d_0_2(
	.DPO(DPO_0[2]),
	.SPO(SPO_0[2]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[2]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 3
//
RAM16X1D ram32x1d_0_3(
	.DPO(DPO_0[3]),
	.SPO(SPO_0[3]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[3]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 4
//
RAM16X1D ram32x1d_0_4(
	.DPO(DPO_0[4]),
	.SPO(SPO_0[4]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[4]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 5
//
RAM16X1D ram32x1d_0_5(
	.DPO(DPO_0[5]),
	.SPO(SPO_0[5]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[5]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 6
//
RAM16X1D ram32x1d_0_6(
	.DPO(DPO_0[6]),
	.SPO(SPO_0[6]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[6]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

//
// Instantiation of block 7
//
RAM16X1D ram32x1d_0_7(
	.DPO(DPO_0[7]),
	.SPO(SPO_0[7]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[7]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_0)
);

RAM16X1D ram32x1d_1_0(
	.DPO(DPO_1[0]),
	.SPO(SPO_1[0]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[0]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 1
//
RAM16X1D ram32x1d_1_1(
	.DPO(DPO_1[1]),
	.SPO(SPO_1[1]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[1]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 2
//
RAM16X1D ram32x1d_1_2(
	.DPO(DPO_1[2]),
	.SPO(SPO_1[2]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[2]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 3
//
RAM16X1D ram32x1d_1_3(
	.DPO(DPO_1[3]),
	.SPO(SPO_1[3]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[3]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 4
//
RAM16X1D ram32x1d_1_4(
	.DPO(DPO_1[4]),
	.SPO(SPO_1[4]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[4]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 5
//
RAM16X1D ram32x1d_1_5(
	.DPO(DPO_1[5]),
	.SPO(SPO_1[5]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[5]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 6
//
RAM16X1D ram32x1d_1_6(
	.DPO(DPO_1[6]),
	.SPO(SPO_1[6]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[6]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);

//
// Instantiation of block 7
//
RAM16X1D ram32x1d_1_7(
	.DPO(DPO_1[7]),
	.SPO(SPO_1[7]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.D(D[7]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.WCLK(WCLK),
	.WE(WE_1)
);
endmodule

`else

module or1200_xcv_ram32x8d (DPO, SPO, A, D, DPRA, WCLK, WE);

//
// I/O
//
output [7:0]	DPO;
output [7:0]	SPO;
input [4:0]	A;
input [4:0]	DPRA;
input [7:0]	D;
input		WCLK;
input		WE;

//
// Instantiation of block 0
//
RAM32X1D ram32x1d_0(
	.DPO(DPO[0]),
	.SPO(SPO[0]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[0]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 1
//
RAM32X1D ram32x1d_1(
	.DPO(DPO[1]),
	.SPO(SPO[1]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[1]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 2
//
RAM32X1D ram32x1d_2(
	.DPO(DPO[2]),
	.SPO(SPO[2]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[2]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 3
//
RAM32X1D ram32x1d_3(
	.DPO(DPO[3]),
	.SPO(SPO[3]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[3]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 4
//
RAM32X1D ram32x1d_4(
	.DPO(DPO[4]),
	.SPO(SPO[4]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[4]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 5
//
RAM32X1D ram32x1d_5(
	.DPO(DPO[5]),
	.SPO(SPO[5]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[5]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 6
//
RAM32X1D ram32x1d_6(
	.DPO(DPO[6]),
	.SPO(SPO[6]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[6]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

//
// Instantiation of block 7
//
RAM32X1D ram32x1d_7(
	.DPO(DPO[7]),
	.SPO(SPO[7]),
	.A0(A[0]),
	.A1(A[1]),
	.A2(A[2]),
	.A3(A[3]),
	.A4(A[4]),
	.D(D[7]),
	.DPRA0(DPRA[0]),
	.DPRA1(DPRA[1]),
	.DPRA2(DPRA[2]),
	.DPRA3(DPRA[3]),
	.DPRA4(DPRA[4]),
	.WCLK(WCLK),
	.WE(WE)
);

endmodule
`endif
`endif
