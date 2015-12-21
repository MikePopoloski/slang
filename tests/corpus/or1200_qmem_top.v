//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's Embedded Memory                                    ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/cores/or1k/                        ////
////                                                              ////
////  Description                                                 ////
////  Embedded Memory               .                             ////
////                                                              ////
////  To Do:                                                      ////
////   - QMEM and IC/DC muxes can be removed except for cycstb    ////
////     (now are is there for easier debugging)                  ////
////   - currently arbitration is slow and stores take 2 clocks   ////
////     (final debugged version will be faster)                  ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2003 Authors and OPENCORES.ORG                 ////
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
// $Log: or1200_qmem_top.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Minor update: 
// Coding style changed.
//
// Revision 1.3  2004/06/08 18:17:36  lampret
// Non-functional changes. Coding style fixes.
//
// Revision 1.2  2004/04/05 08:40:26  lampret
// Merged branch_qmem into main tree.
//
// Revision 1.1.2.4  2004/01/11 22:45:46  andreje
// Separate instruction and data QMEM decoders, QMEM acknowledge and byte-select added
//
// Revision 1.1.2.3  2003/12/17 13:36:58  simons
// Qmem mbist signals fixed.
//
// Revision 1.1.2.2  2003/12/09 11:46:48  simons
// Mbist nameing changed, Artisan ram instance signal names fixed, some synthesis waning fixed.
//
// Revision 1.1.2.1  2003/07/08 15:45:26  lampret
// Added embedded memory QMEM.
//
//

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

`define OR1200_QMEMFSM_IDLE	3'd0
`define OR1200_QMEMFSM_STORE	3'd1
`define OR1200_QMEMFSM_LOAD	3'd2
`define OR1200_QMEMFSM_FETCH	3'd3

//
// Embedded memory
//
module or1200_qmem_top(
	// Rst, clk and clock control
	clk, rst,

`ifdef OR1200_BIST
	// RAM BIST
	mbist_si_i, mbist_so_o, mbist_ctrl_i,
`endif

	// QMEM and CPU/IMMU
	qmemimmu_adr_i,
	qmemimmu_cycstb_i,
	qmemimmu_ci_i,
	qmemicpu_sel_i,
	qmemicpu_tag_i,
	qmemicpu_dat_o,
	qmemicpu_ack_o,
	qmemimmu_rty_o,
	qmemimmu_err_o,
	qmemimmu_tag_o,

	// QMEM and IC
	icqmem_adr_o,
	icqmem_cycstb_o,
	icqmem_ci_o,
	icqmem_sel_o,
	icqmem_tag_o,
	icqmem_dat_i,
	icqmem_ack_i,
	icqmem_rty_i,
	icqmem_err_i,
	icqmem_tag_i,

	// QMEM and CPU/DMMU
	qmemdmmu_adr_i,
	qmemdmmu_cycstb_i,
	qmemdmmu_ci_i,
	qmemdcpu_we_i,
	qmemdcpu_sel_i,
	qmemdcpu_tag_i,
	qmemdcpu_dat_i,
	qmemdcpu_dat_o,
	qmemdcpu_ack_o,
	qmemdcpu_rty_o,
	qmemdmmu_err_o,
	qmemdmmu_tag_o,

	// QMEM and DC
	dcqmem_adr_o,
	dcqmem_cycstb_o,
	dcqmem_ci_o,
	dcqmem_we_o,
	dcqmem_sel_o,
	dcqmem_tag_o,
	dcqmem_dat_o,
	dcqmem_dat_i,
	dcqmem_ack_i,
	dcqmem_rty_i,
	dcqmem_err_i,
	dcqmem_tag_i 

);

parameter dw = `OR1200_OPERAND_WIDTH;

//
// I/O
//

//
// Clock and reset
//
input				clk;
input				rst;

`ifdef OR1200_BIST
//
// RAM BIST
//
input mbist_si_i;
input [`OR1200_MBIST_CTRL_WIDTH - 1:0] mbist_ctrl_i;
output mbist_so_o;
`endif

//
// QMEM and CPU/IMMU
//
input	[31:0]			qmemimmu_adr_i;
input				qmemimmu_cycstb_i;
input				qmemimmu_ci_i;
input	[3:0]			qmemicpu_sel_i;
input	[3:0]			qmemicpu_tag_i;
output	[31:0]			qmemicpu_dat_o;
output				qmemicpu_ack_o;
output				qmemimmu_rty_o;
output				qmemimmu_err_o;
output	[3:0]			qmemimmu_tag_o;

//
// QMEM and IC
//
output	[31:0]			icqmem_adr_o;
output				icqmem_cycstb_o;
output				icqmem_ci_o;
output	[3:0]			icqmem_sel_o;
output	[3:0]			icqmem_tag_o;
input	[31:0]			icqmem_dat_i;
input				icqmem_ack_i;
input				icqmem_rty_i;
input				icqmem_err_i;
input	[3:0]			icqmem_tag_i;

//
// QMEM and CPU/DMMU
//
input	[31:0]			qmemdmmu_adr_i;
input				qmemdmmu_cycstb_i;
input				qmemdmmu_ci_i;
input				qmemdcpu_we_i;
input	[3:0]			qmemdcpu_sel_i;
input	[3:0]			qmemdcpu_tag_i;
input	[31:0]			qmemdcpu_dat_i;
output	[31:0]			qmemdcpu_dat_o;
output				qmemdcpu_ack_o;
output				qmemdcpu_rty_o;
output				qmemdmmu_err_o;
output	[3:0]			qmemdmmu_tag_o;

//
// QMEM and DC
//
output	[31:0]			dcqmem_adr_o;
output				dcqmem_cycstb_o;
output				dcqmem_ci_o;
output				dcqmem_we_o;
output	[3:0]			dcqmem_sel_o;
output	[3:0]			dcqmem_tag_o;
output	[dw-1:0]		dcqmem_dat_o;
input	[dw-1:0]		dcqmem_dat_i;
input				dcqmem_ack_i;
input				dcqmem_rty_i;
input				dcqmem_err_i;
input	[3:0]			dcqmem_tag_i;

`ifdef OR1200_QMEM_IMPLEMENTED

//
// Internal regs and wires
//
wire				iaddr_qmem_hit;
wire				daddr_qmem_hit;
reg	[2:0]			state;
reg				qmem_dack;
reg				qmem_iack;
wire	[31:0]			qmem_di;
wire	[31:0]			qmem_do;
wire				qmem_en;
wire				qmem_we;
`ifdef OR1200_QMEM_BSEL
wire  [3:0]       qmem_sel;
`endif
wire	[31:0]			qmem_addr;
`ifdef OR1200_QMEM_ACK
wire              qmem_ack;
`else
wire              qmem_ack = 1'b1;
`endif

//
// QMEM and CPU/IMMU
//
assign qmemicpu_dat_o = qmem_iack ? qmem_do : icqmem_dat_i;
assign qmemicpu_ack_o = qmem_iack ? 1'b1 : icqmem_ack_i;
assign qmemimmu_rty_o = qmem_iack ? 1'b0 : icqmem_rty_i;
assign qmemimmu_err_o = qmem_iack ? 1'b0 : icqmem_err_i;
assign qmemimmu_tag_o = qmem_iack ? 4'h0 : icqmem_tag_i;

//
// QMEM and IC
//
assign icqmem_adr_o = iaddr_qmem_hit ? 32'h0000_0000 : qmemimmu_adr_i;
assign icqmem_cycstb_o = iaddr_qmem_hit ? 1'b0 : qmemimmu_cycstb_i;
assign icqmem_ci_o = iaddr_qmem_hit ? 1'b0 : qmemimmu_ci_i;
assign icqmem_sel_o = iaddr_qmem_hit ? 4'h0 : qmemicpu_sel_i;
assign icqmem_tag_o = iaddr_qmem_hit ? 4'h0 : qmemicpu_tag_i;

//
// QMEM and CPU/DMMU
//
assign qmemdcpu_dat_o = daddr_qmem_hit ? qmem_do : dcqmem_dat_i;
assign qmemdcpu_ack_o = daddr_qmem_hit ? qmem_dack : dcqmem_ack_i;
assign qmemdcpu_rty_o = daddr_qmem_hit ? ~qmem_dack : dcqmem_rty_i;
assign qmemdmmu_err_o = daddr_qmem_hit ? 1'b0 : dcqmem_err_i;
assign qmemdmmu_tag_o = daddr_qmem_hit ? 4'h0 : dcqmem_tag_i;

//
// QMEM and DC
//
assign dcqmem_adr_o = daddr_qmem_hit ? 32'h0000_0000 : qmemdmmu_adr_i;
assign dcqmem_cycstb_o = daddr_qmem_hit ? 1'b0 : qmemdmmu_cycstb_i;
assign dcqmem_ci_o = daddr_qmem_hit ? 1'b0 : qmemdmmu_ci_i;
assign dcqmem_we_o = daddr_qmem_hit ? 1'b0 : qmemdcpu_we_i;
assign dcqmem_sel_o = daddr_qmem_hit ? 4'h0 : qmemdcpu_sel_i;
assign dcqmem_tag_o = daddr_qmem_hit ? 4'h0 : qmemdcpu_tag_i;
assign dcqmem_dat_o = daddr_qmem_hit ? 32'h0000_0000 : qmemdcpu_dat_i;

//
// Address comparison whether QMEM was hit
//
`ifdef OR1200_QMEM_IADDR
assign iaddr_qmem_hit = (qmemimmu_adr_i & `OR1200_QMEM_IMASK) == `OR1200_QMEM_IADDR;
`else
assign iaddr_qmem_hit = 1'b0;
`endif

`ifdef OR1200_QMEM_DADDR
assign daddr_qmem_hit = (qmemdmmu_adr_i & `OR1200_QMEM_DMASK) == `OR1200_QMEM_DADDR;
`else
assign daddr_qmem_hit = 1'b0;
`endif

//
//
//
assign qmem_en = iaddr_qmem_hit & qmemimmu_cycstb_i | daddr_qmem_hit & qmemdmmu_cycstb_i;
assign qmem_we = qmemdmmu_cycstb_i & daddr_qmem_hit & qmemdcpu_we_i;
`ifdef OR1200_QMEM_BSEL
assign qmem_sel = (qmemdmmu_cycstb_i & daddr_qmem_hit) ? qmemdcpu_sel_i : qmemicpu_sel_i;
`endif
assign qmem_di = qmemdcpu_dat_i;
assign qmem_addr = (qmemdmmu_cycstb_i & daddr_qmem_hit) ? qmemdmmu_adr_i : qmemimmu_adr_i;

//
// QMEM control FSM
//
always @(`OR1200_RST_EVENT rst or posedge clk)
	if (rst == `OR1200_RST_VALUE) begin
		state <=  `OR1200_QMEMFSM_IDLE;
		qmem_dack <=  1'b0;
		qmem_iack <=  1'b0;
	end
	else case (state)	// synopsys parallel_case
		`OR1200_QMEMFSM_IDLE: begin
			if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmemdcpu_we_i & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_STORE;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_LOAD;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemimmu_cycstb_i & iaddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_FETCH;
				qmem_iack <=  1'b1;
				qmem_dack <=  1'b0;
			end
		end
		`OR1200_QMEMFSM_STORE: begin
			if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmemdcpu_we_i & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_STORE;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_LOAD;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemimmu_cycstb_i & iaddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_FETCH;
				qmem_iack <=  1'b1;
				qmem_dack <=  1'b0;
			end
			else begin
				state <=  `OR1200_QMEMFSM_IDLE;
				qmem_dack <=  1'b0;
				qmem_iack <=  1'b0;
			end
		end
		`OR1200_QMEMFSM_LOAD: begin
			if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmemdcpu_we_i & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_STORE;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_LOAD;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemimmu_cycstb_i & iaddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_FETCH;
				qmem_iack <=  1'b1;
				qmem_dack <=  1'b0;
			end
			else begin
				state <=  `OR1200_QMEMFSM_IDLE;
				qmem_dack <=  1'b0;
				qmem_iack <=  1'b0;
			end
		end
		`OR1200_QMEMFSM_FETCH: begin
			if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmemdcpu_we_i & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_STORE;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemdmmu_cycstb_i & daddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_LOAD;
				qmem_dack <=  1'b1;
				qmem_iack <=  1'b0;
			end
			else if (qmemimmu_cycstb_i & iaddr_qmem_hit & qmem_ack) begin
				state <=  `OR1200_QMEMFSM_FETCH;
				qmem_iack <=  1'b1;
				qmem_dack <=  1'b0;
			end
			else begin
				state <=  `OR1200_QMEMFSM_IDLE;
				qmem_dack <=  1'b0;
				qmem_iack <=  1'b0;
			end
		end
		default: begin
			state <=  `OR1200_QMEMFSM_IDLE;
			qmem_dack <=  1'b0;
			qmem_iack <=  1'b0;
		end
	endcase

//
// Instantiation of embedded memory
//
or1200_spram_2048x32 or1200_qmem_ram(
	.clk(clk),
	.rst(rst),
`ifdef OR1200_BIST
	// RAM BIST
	.mbist_si_i(mbist_si_i),
	.mbist_so_o(mbist_so_o),
	.mbist_ctrl_i(mbist_ctrl_i),
`endif
	.addr(qmem_addr[12:2]),
`ifdef OR1200_QMEM_BSEL
	.sel(qmem_sel),
`endif
`ifdef OR1200_QMEM_ACK
  .ack(qmem_ack),
`endif
  .ce(qmem_en),
	.we(qmem_we),
	.oe(1'b1),
	.di(qmem_di),
	.doq(qmem_do)
);

`else  // OR1200_QMEM_IMPLEMENTED

//
// QMEM and CPU/IMMU
//
assign qmemicpu_dat_o = icqmem_dat_i;
assign qmemicpu_ack_o = icqmem_ack_i;
assign qmemimmu_rty_o = icqmem_rty_i;
assign qmemimmu_err_o = icqmem_err_i;
assign qmemimmu_tag_o = icqmem_tag_i;

//
// QMEM and IC
//
assign icqmem_adr_o = qmemimmu_adr_i;
assign icqmem_cycstb_o = qmemimmu_cycstb_i;
assign icqmem_ci_o = qmemimmu_ci_i;
assign icqmem_sel_o = qmemicpu_sel_i;
assign icqmem_tag_o = qmemicpu_tag_i;

//
// QMEM and CPU/DMMU
//
assign qmemdcpu_dat_o = dcqmem_dat_i;
assign qmemdcpu_ack_o = dcqmem_ack_i;
assign qmemdcpu_rty_o = dcqmem_rty_i;
assign qmemdmmu_err_o = dcqmem_err_i;
assign qmemdmmu_tag_o = dcqmem_tag_i;

//
// QMEM and DC
//
assign dcqmem_adr_o = qmemdmmu_adr_i;
assign dcqmem_cycstb_o = qmemdmmu_cycstb_i;
assign dcqmem_ci_o = qmemdmmu_ci_i;
assign dcqmem_we_o = qmemdcpu_we_i;
assign dcqmem_sel_o = qmemdcpu_sel_i;
assign dcqmem_tag_o = qmemdcpu_tag_i;
assign dcqmem_dat_o = qmemdcpu_dat_i;

`ifdef OR1200_BIST
assign mbist_so_o = mbist_si_i;
`endif

`endif

endmodule
