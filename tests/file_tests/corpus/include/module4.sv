interface interface4
#(
    parameter int P
)
(
    input logic     clk,
    input logic     rst
);

    logic            valid;
    logic [P-1:0]    data;
    logic            ack;

endinterface

module helper4_master
(
    interface4  master
);

    localparam mP = master.P;

    always_ff @(posedge master.clk) begin
        if (master.ack) begin
            master.valid <= '1;
            master.data <= master.data + 1'd1;
        end
    end

endmodule

module helper4_slave
(
    interface4  slave
);

    localparam sP = slave.P;

    always_ff @(posedge slave.clk) begin
        slave.ack <= ~slave.ack;
    end

endmodule

module module4;

    localparam LP = 3;

    logic clk, rst;

    interface4 #(LP) i (.*);

    helper4_master
    helper_master (
        .master (i)
    );

    helper4_slave
    helper_slave (i);

endmodule
