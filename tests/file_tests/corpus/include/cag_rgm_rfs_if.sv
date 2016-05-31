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
 */

//
//
// register file interface
//
//

`ifndef CAG_RGM_RFS_IF_SV
`define CAG_RGM_RFS_IF_SV

interface cag_rgm_rfs_if #(
        parameter ADDR_WIDTH       = 6,
        parameter WRITE_DATA_WIDTH = 64,
        parameter READ_DATA_WIDTH  = 64
    ) ();

    logic res_n;
    logic clk;

    logic [ADDR_WIDTH-1:0]       address;
    logic                        wen;
    logic                        ren;
    logic [WRITE_DATA_WIDTH-1:0] write_data;
    logic [READ_DATA_WIDTH-1:0]  read_data;
    logic                        access_done;
    logic                        invalid_address;

    property valid_wen;
        @(posedge clk) disable iff(!res_n)
        wen |-> !$isunknown(address) && !$isunknown(write_data);
    endproperty : valid_wen
    assert property(valid_wen);


    property valid_ren;
        @(posedge clk) disable iff(!res_n)
        ren |-> !$isunknown(address);
    endproperty : valid_ren
    assert property(valid_ren);


    property valid_access_done;
        @(posedge clk) disable iff(!res_n)
        wen || ren |=> !(wen || ren) [*0:1150] ##1 access_done;
    endproperty : valid_access_done
    assert property(valid_access_done);

    access_done_one_clk : assert property(@(posedge clk) disable iff(!res_n) $rose(access_done) |=> !access_done );

    property invalid_address_on_done_only;
        @(posedge clk) disable iff(!res_n)
        invalid_address |-> access_done;
    endproperty : invalid_address_on_done_only
    assert property(invalid_address_on_done_only);

    property no_simultaneous_read_and_write_on_0;
        @(posedge clk) disable iff(!res_n)
        ren |-> !wen;
    endproperty : no_simultaneous_read_and_write_on_0
    assert property(no_simultaneous_read_and_write_on_0);

    property no_simultaneous_read_and_write_on_1;
        @(posedge clk) disable iff(!res_n)
        wen |-> !ren;
    endproperty : no_simultaneous_read_and_write_on_1
    assert property(no_simultaneous_read_and_write_on_1);

endinterface : cag_rgm_rfs_if

`endif // CAG_RGM_RFS_IF_SV
