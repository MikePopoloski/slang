/*
 *                              .--------------. .----------------. .------------.
 *                             | .------------. | .--------------. | .----------. |
 *                             | | ____  ____ | | | ____    ____ | | |   ______ | |
 *                             | ||_   ||   _|| | ||_   \  /   _|| | | .' ___  || |
 *       ___  _ __   ___ _ __  | |  | |__| |  | | |  |   \/   |  | | |/ .'   \_|| |
 *      / _ \| '_ \ / _ \ '_ \ | |  |  __  |  | | |  | |\  /| |  | | || |       | |
 *       (_) | |_) |  __/ | | || | _| |  | |_ | | | _| |_\/_| |_ | | |\ `.___.'\| |
 *      \___/| .__/ \___|_| |_|| ||____||____|| | ||_____||_____|| | | `._____.'| |
 *           | |               | |            | | |              | | |          | |
 *           |_|               | '------------' | '--------------' | '----------' |
 *                              '--------------' '----------------' '------------'
 *
 *  openHMC - An Open Source Hybrid Memory Cube Controller
 *  (C) Copyright 2014 Computer Architecture Group - University of Heidelberg
 *  www.ziti.uni-heidelberg.de
 *  B6, 26
 *  68159 Mannheim
 *  Germany
 *
 *  Contact: openhmc@ziti.uni-heidelberg.de
 *  http://ra.ziti.uni-heidelberg.de/openhmc
 *
 *   This source file is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This source file is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with this source file.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *  Module name: crc_accu
 */

module crc_accu #(parameter FPW=4)(
    //----------------------------------
    //----SYSTEM INTERFACE
    //----------------------------------
    input  wire         clk,
    input  wire         res_n,

    //----------------------------------
    //----Input
    //----------------------------------
    input  wire [FPW-1:0]       tail,
    input  wire [(FPW*32)-1:0]  d_in,

    //----------------------------------
    //----Output
    //----------------------------------
    output reg  [31:0]          crc_out
);

integer i_f;

reg  [31:0]    crc_temp [FPW:0];
wire [31:0]    in [FPW-1:0];


genvar f;
generate
    for(f=0;f<FPW;f=f+1) begin
        assign in[f] = d_in[(f*32)+32-1:(f*32)];
    end
endgenerate
 

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n) `else
always @(posedge clk) `endif
begin
`ifdef RESET_ALL
    if (!res_n) begin
            crc_out <= 32'h0;
    end else 
`endif
begin
    crc_out <= 32'h0;
    for(i_f=0;i_f<FPW;i_f=i_f+1) begin
        if(tail[i_f]) begin
            crc_out <= crc_temp[i_f+1];
        end
    end
end
end

`ifdef ASYNC_RES
always @(posedge clk or negedge res_n) `else
always @(posedge clk) `endif
begin
    if (!res_n) 
        crc_temp[0] <= 32'h0;
    else 
        crc_temp[0] <= |tail ? 32'h0 : crc_temp[FPW];
end

always @(*)
begin
    for(i_f=0;i_f<FPW;i_f=i_f+1) begin
        crc_temp[i_f+1][31] = in[i_f][31] ^ crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][8]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][21]^crc_temp[i_f][26]^crc_temp[i_f][29];
        crc_temp[i_f+1][30] = in[i_f][30] ^ crc_temp[i_f][2]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][7]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][20]^crc_temp[i_f][25]^crc_temp[i_f][28];
        crc_temp[i_f+1][29] = in[i_f][29] ^ crc_temp[i_f][1]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][21]^crc_temp[i_f][24]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][29];
        crc_temp[i_f+1][28] = in[i_f][28] ^ crc_temp[i_f][0]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][9]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][23]^crc_temp[i_f][25]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][31];
        crc_temp[i_f+1][27] = in[i_f][27] ^ crc_temp[i_f][4]^crc_temp[i_f][6]^crc_temp[i_f][10]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][22]^crc_temp[i_f][24]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][26] = in[i_f][26] ^ crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][9]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][23]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][25] = in[i_f][25] ^ crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][22]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][24] = in[i_f][24] ^ crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][29]^crc_temp[i_f][30];
        crc_temp[i_f+1][23] = in[i_f][23] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][15]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][28]^crc_temp[i_f][29];
        crc_temp[i_f+1][22] = in[i_f][22] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][14]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][21]^crc_temp[i_f][22]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][27]^crc_temp[i_f][28];
        crc_temp[i_f+1][21] = in[i_f][21] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][13]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][26]^crc_temp[i_f][27];
        crc_temp[i_f+1][20] = in[i_f][20] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][7]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][12]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][31];
        crc_temp[i_f+1][19] = in[i_f][19] ^ crc_temp[i_f][0]^crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][7]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][22]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][29]^crc_temp[i_f][30];
        crc_temp[i_f+1][18] = in[i_f][18] ^ crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][28];
        crc_temp[i_f+1][17] = in[i_f][17] ^ crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][13]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][27]^crc_temp[i_f][31];
        crc_temp[i_f+1][16] = in[i_f][16] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][7]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][15] = in[i_f][15] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][9]^crc_temp[i_f][14]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][26]^crc_temp[i_f][28]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][14] = in[i_f][14] ^ crc_temp[i_f][0]^crc_temp[i_f][2]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][13] = in[i_f][13] ^ crc_temp[i_f][1]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][21]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][29]^crc_temp[i_f][30];
        crc_temp[i_f+1][12] = in[i_f][12] ^ crc_temp[i_f][0]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][20]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][31];
        crc_temp[i_f+1][11] = in[i_f][11] ^ crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][7]^crc_temp[i_f][8]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][14]^crc_temp[i_f][16]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][30];
        crc_temp[i_f+1][10] = in[i_f][10] ^ crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][7]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][17]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][27];
        crc_temp[i_f+1][ 9] = in[i_f][ 9] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][7]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][19]^crc_temp[i_f][22]^crc_temp[i_f][29]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 8] = in[i_f][ 8] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][6]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][21]^crc_temp[i_f][28]^crc_temp[i_f][30];
        crc_temp[i_f+1][ 7] = in[i_f][ 7] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][20]^crc_temp[i_f][27]^crc_temp[i_f][29]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 6] = in[i_f][ 6] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][7]^crc_temp[i_f][9]^crc_temp[i_f][12]^crc_temp[i_f][13]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][21]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 5] = in[i_f][ 5] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][4]^crc_temp[i_f][10]^crc_temp[i_f][12]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][21]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][30];
        crc_temp[i_f+1][ 4] = in[i_f][ 4] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][3]^crc_temp[i_f][9]^crc_temp[i_f][11]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][25]^crc_temp[i_f][26]^crc_temp[i_f][27]^crc_temp[i_f][29]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 3] = in[i_f][ 3] ^ crc_temp[i_f][0]^crc_temp[i_f][2]^crc_temp[i_f][3]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][11]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][21]^crc_temp[i_f][24]^crc_temp[i_f][25]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 2] = in[i_f][ 2] ^ crc_temp[i_f][1]^crc_temp[i_f][2]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][10]^crc_temp[i_f][14]^crc_temp[i_f][15]^crc_temp[i_f][20]^crc_temp[i_f][23]^crc_temp[i_f][24]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][29]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 1] = in[i_f][ 1] ^ crc_temp[i_f][0]^crc_temp[i_f][1]^crc_temp[i_f][4]^crc_temp[i_f][5]^crc_temp[i_f][6]^crc_temp[i_f][8]^crc_temp[i_f][9]^crc_temp[i_f][10]^crc_temp[i_f][11]^crc_temp[i_f][13]^crc_temp[i_f][15]^crc_temp[i_f][17]^crc_temp[i_f][18]^crc_temp[i_f][21]^crc_temp[i_f][22]^crc_temp[i_f][23]^crc_temp[i_f][27]^crc_temp[i_f][28]^crc_temp[i_f][30]^crc_temp[i_f][31];
        crc_temp[i_f+1][ 0] = in[i_f][ 0] ^ crc_temp[i_f][0]^crc_temp[i_f][4]^crc_temp[i_f][6]^crc_temp[i_f][7]^crc_temp[i_f][9]^crc_temp[i_f][11]^crc_temp[i_f][12]^crc_temp[i_f][15]^crc_temp[i_f][16]^crc_temp[i_f][18]^crc_temp[i_f][19]^crc_temp[i_f][20]^crc_temp[i_f][22]^crc_temp[i_f][27]^crc_temp[i_f][30];
    end
end

endmodule
