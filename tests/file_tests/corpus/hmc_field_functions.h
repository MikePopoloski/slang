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
 *  File name: hmc_field_functions.h
 *
 */

//------------------------------------------------------------------------HMC HEADER FIELDS
 
 function [5:0] cmd;
    input [127:0] flit;

    begin
        cmd = flit[5:0];
    end
 endfunction

 function [5:0] num_requested_flits;
    input [127:0] flit;

    begin
        num_requested_flits = flit[2:0] + 2;    //+1 for the encoding
    end
 endfunction
 
 function [2:0] flow_cmd;
    input [127:0] flit;

    begin
        flow_cmd = flit[2:0];
    end
 endfunction

 function [2:0] cmd_type;
    input [127:0] flit;

    begin
        cmd_type = flit[5:3];
    end
 endfunction

 function is_req_flow;
    input [127:0] flit;
    begin
        //according to spec it should check for bits [5:2]. However, all regular requests have bit 3,4 or 5 set so we reduce logic by checking only these
        if(flit[5:3]) begin 
            is_req_flow = 0;
        end else begin
            is_req_flow = 1;
        end
    end
 endfunction

 function is_rsp_flow;
    input [127:0] flit;
    begin
        //according to spec it should check for bits [5:2]. However, all responses have bit 5 set so we reduce logic by only checking this single bit
        if(flit[5]) begin 
            is_rsp_flow = 0;
        end else begin
            is_rsp_flow = 1;
        end
    end
 endfunction

  function lng_dln_equal;
    input [127:0] flit;
    begin
        if(!(lng(flit)^dln(flit))) begin
            lng_dln_equal = 1;
        end else begin
            lng_dln_equal = 0;
        end
    end
 endfunction

 function irtry_start_retry_flag;
    input [127:0] flit;

    begin
        irtry_start_retry_flag = flit[64+8];
    end
 endfunction

 function irtry_clear_error_flag;
    input [127:0] flit;

    begin
        irtry_clear_error_flag = flit[64+8+1];
    end
 endfunction
  
 function [3:0] lng;
    input [127:0] flit;

    begin
        lng = flit[10:7];
    end
 endfunction
 
  
 function [3:0] dln;
    input [127:0]   flit;

    begin
        dln = flit[14:11];
    end
 endfunction
 
  
 function [8:0] tag;
    input [127:0] flit;

    begin
        tag = flit[23:15];
    end
 endfunction
 
 function [57:24] adrs;
    input [127:0] flit;

    begin
        adrs = flit[57:24];
    end
 endfunction

 function [2:0] cub;
    input [127:0] flit;

    begin
        cub = flit[63:61];
    end
 endfunction
 
//------------------------------------------------------------------------HMC TAIL FIELDS
 
 function [7:0] rrp;
    input [127:0]   flit;

    begin
        rrp = flit[64+7:64];
    end
 endfunction

 function [7:0] frp;
    input [127:0]   flit;

    begin
        frp = flit[64+15:64+8];
    end
 endfunction
 
 function [2:0] seq;
        input [127:0]   flit;

        begin
                seq = flit[64+18:64+16];
        end
 endfunction
 
 function [6:0] errstat;
        input [127:0]   flit;

        begin
                errstat = flit[64+26:64+20];
        end
 endfunction

 function [4:0] rtc;
        input [127:0]   flit;

        begin
                rtc = flit[64+31:64+27];
        end
 endfunction
 
 function [31:0] crc;
    input [127:0]   flit;

    begin
        crc = flit[127:128-32];
    end
 endfunction
 

 
 