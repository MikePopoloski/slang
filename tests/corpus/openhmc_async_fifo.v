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
 *  Module name: openhmc_async_fifo
 *
 */

`default_nettype none

module openhmc_async_fifo #(
        parameter DWIDTH                        = 8,
        parameter ENTRIES                       = 2,
        parameter DISABLE_FULL_ASSERT           = 0,
        parameter DISABLE_EMPTY_ASSERT          = 0,
        parameter DISABLE_SHIFT_OUT_ASSERT      = 0,
        parameter DISABLE_SHIFT_IN_ASSERT       = 0,
        parameter DISABLE_SO_DATA_KNOWN_ASSERT  = 0
    ) (
        // interface for shift_in side
        input wire              si_clk,
        input wire              si_res_n,
        input wire              shift_in,
        input wire [DWIDTH-1:0] d_in,

        output reg              full,
        output reg              almost_full,

        // interface for shift_out side
        input wire              so_clk,
        input wire              so_res_n,
        input wire              shift_out,

        output reg [DWIDTH-1:0] d_out,
        output reg              empty,
        output reg              almost_empty
    );

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------WIRING AND SIGNAL STUFF---------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

// the FIFO currently can only have up to 2048 entries
    localparam LG_ENTRIES = (ENTRIES <= 2)    ?  1 :
                            (ENTRIES <= 4)    ?  2 :
                            (ENTRIES <= 8)    ?  3 :
                            (ENTRIES <= 16)   ?  4 :
                            (ENTRIES <= 32)   ?  5 :
                            (ENTRIES <= 64)   ?  6 :
                            (ENTRIES <= 128)  ?  7 :
                            (ENTRIES <= 256)  ?  8 :
                            (ENTRIES <= 512)  ?  9 :
                            (ENTRIES <= 1024) ? 10 : 11;

    reg [DWIDTH-1:0]            entry [0:ENTRIES-1];

    reg [LG_ENTRIES-1:0]    wp;
    reg [LG_ENTRIES-1:0]    rp;

    // asynchronous thermo wp
    reg [ENTRIES-1:0]       thermo_wp_w;
    reg [ENTRIES-1:0]       thermo_rp_w;

    reg [ENTRIES-1:0]       thermo_wp;
    reg [ENTRIES-1:0]       thermo_rp;

    reg [ENTRIES-1:0]       thermo_wp_synced_0;

    reg [ENTRIES-1:0]       thermo_wp_synced_1;

    reg [ENTRIES-1:0]       thermo_rp_synced_0;

    reg [ENTRIES-1:0]       thermo_rp_synced_1;

    wire [LG_ENTRIES-1:0]   next_rp;
    wire [LG_ENTRIES-1:0]   next_rp_p1;

    wire                    set_empty_w;
    wire                    set_a_empty_0_w;
    wire                    set_a_empty_1_w;
    wire                    set_a_empty_2_w;

    wire                    set_full_w;
    wire                    set_a_full_0_w;
    wire                    set_a_full_1_w;
    wire                    set_a_full_2_w;

    wire [LG_ENTRIES-1:0]   upper_bound;

    assign next_rp          = (rp == upper_bound) ? {LG_ENTRIES {1'b0}} : rp + 1'b1;
    assign next_rp_p1       = (next_rp == upper_bound) ? {LG_ENTRIES {1'b0}} : next_rp + 1'b1;

    assign set_empty_w      = (thermo_rp == thermo_wp_synced_1);
    assign set_a_empty_0_w  = (thermo_rp == {~thermo_wp_synced_1[0],   thermo_wp_synced_1[ENTRIES-1:1]});
    assign set_a_empty_1_w  = (thermo_rp == {~thermo_wp_synced_1[1:0], thermo_wp_synced_1[ENTRIES-1:2]});
    assign set_a_empty_2_w  = (thermo_rp == {~thermo_wp_synced_1[2:0], thermo_wp_synced_1[ENTRIES-1:3]});

    assign set_full_w       = &(thermo_wp ^ thermo_rp_synced_1);
    assign set_a_full_0_w   = &(thermo_wp ^ {~thermo_rp_synced_1[0],   thermo_rp_synced_1[ENTRIES-1:1]});
    assign set_a_full_1_w   = &(thermo_wp ^ {~thermo_rp_synced_1[1:0], thermo_rp_synced_1[ENTRIES-1:2]});
    assign set_a_full_2_w   = &(thermo_wp ^ {~thermo_rp_synced_1[2:0], thermo_rp_synced_1[ENTRIES-1:3]});

    assign upper_bound      = ENTRIES[LG_ENTRIES-1:0] - {{LG_ENTRIES-1 {1'b0}}, 1'b1};

    always @ (*)
    begin
        if (shift_in && !full)
            thermo_wp_w     = {thermo_wp[ENTRIES-2:0], !thermo_wp[ENTRIES-1]};
        else
            thermo_wp_w     = thermo_wp;
    end

    always @ (*)
    begin
        if (shift_out && !empty)
            thermo_rp_w     = {thermo_rp[ENTRIES-2:0], !thermo_rp[ENTRIES-1]};
        else
            thermo_rp_w     = thermo_rp;
    end

//=====================================================================================================
//-----------------------------------------------------------------------------------------------------
//---------LOGIC STARTS HERE---------------------------------------------------------------------------
//-----------------------------------------------------------------------------------------------------
//=====================================================================================================

    // shift_in side:
    `ifdef ASYNC_RES
    always @(posedge si_clk or negedge si_res_n) `else
    always @(posedge si_clk) `endif
    begin
        if (!si_res_n)
        begin
            wp                  <= {LG_ENTRIES {1'b0}};
            thermo_wp           <= {ENTRIES {1'b0}};
            full                <= 1'b0;
            almost_full         <= 1'b0;
        end
        else
        begin
            full                <= set_full_w || (set_a_full_0_w && shift_in) ;
            almost_full         <= set_full_w || (set_a_full_0_w) || (set_a_full_1_w && shift_in) ;

            thermo_wp           <= thermo_wp_w;

            if (shift_in && !full)
            begin
                entry[wp]       <= d_in;

                if (wp == upper_bound)
                    wp          <= {LG_ENTRIES {1'b0}};
                else
                    wp          <= wp + 1'b1;
            end
        end
    end

    // shift_out side
    `ifdef ASYNC_RES
    always @(posedge so_clk or negedge so_res_n) `else
    always @(posedge so_clk) `endif
    begin
        if (!so_res_n)
        begin
            rp                  <= {LG_ENTRIES {1'b0}};
            thermo_rp           <= {ENTRIES {1'b0}};
            empty               <= 1'b1;
            almost_empty        <= 1'b1;

        end
        else
        begin
            empty               <= (set_empty_w || (set_a_empty_0_w && shift_out && !empty));
            almost_empty        <= empty || set_empty_w || set_a_empty_0_w || (set_a_empty_1_w && shift_out && !empty);

            thermo_rp           <= thermo_rp_w;
            // shift out and not empty or empty but a new word just finished synchronizing (like almost empty)
            if (shift_out && !empty)
            begin
                rp              <= next_rp;
                d_out       <= entry[next_rp];
            end
            else
            begin
                d_out       <= entry[rp];
            end
        end
    end

    // syncing thermp_rp to shift_in domain
    `ifdef ASYNC_RES
    always @(posedge si_clk or negedge si_res_n) `else
    always @(posedge si_clk) `endif
    begin
        if (!si_res_n)
        begin
            thermo_rp_synced_0  <= {ENTRIES {1'b0}};
            thermo_rp_synced_1  <= {ENTRIES {1'b0}};
        end
        else
        begin
            thermo_rp_synced_0  <= thermo_rp;
            thermo_rp_synced_1  <= thermo_rp_synced_0;
        end
    end

    // syncing write pointer to shift_out domain
    `ifdef ASYNC_RES
    always @(posedge so_clk or negedge so_res_n) `else
    always @(posedge so_clk) `endif
    begin
        if (!so_res_n)
        begin
            thermo_wp_synced_0  <= {ENTRIES {1'b0}};
            thermo_wp_synced_1  <= {ENTRIES {1'b0}};
        end
        else
        begin
            thermo_wp_synced_0  <= thermo_wp;
            thermo_wp_synced_1  <= thermo_wp_synced_0;
        end
    end


`ifdef CAG_ASSERTIONS
    shift_in_and_full:      assert property (@(posedge si_clk) disable iff(!si_res_n) (shift_in |-> !full));

    if (DISABLE_SHIFT_OUT_ASSERT == 0)
        shift_out_and_empty:    assert property (@(posedge so_clk) disable iff(!so_res_n) (shift_out |-> !empty));

    if (DISABLE_SO_DATA_KNOWN_ASSERT == 0) begin
        dout_known:             assert property (@(posedge so_clk) disable iff(!so_res_n) (!empty |-> !$isunknown(d_out)));
    end

    final
    begin
        if (DISABLE_FULL_ASSERT == 0)
        begin
            full_set_assert:                assert (!full);
        end

        if (DISABLE_EMPTY_ASSERT == 0)
        begin
            almost_empty_not_set_assert:    assert (almost_empty);
            empty_not_set_assert:           assert (empty);
        end
    end
`endif // CAG_ASSERTIONS

endmodule

`default_nettype wire
