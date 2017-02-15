package Foo_pkg;

    parameter PI = 3;

endpackage

package Bar_pkg;

    parameter E = 2;
    parameter F = 5;
endpackage

package Baz_pkg;

    parameter ZERO = 0, ONE = 1;
    parameter TWO = 2, THREE = 3;

endpackage

module module3A;
    import Foo_pkg::*;
    import Bar_pkg::E;

    localparam LP1 = PI;
    localparam LP2 = E; // F will give error here
    localparam LP3 = Baz_pkg::ZERO;

endmodule

module module3B
    import Baz_pkg::ONE,
           Baz_pkg::TWO;
(
    input   [ONE-1:0] in1
);

    localparam LP1 = TWO;

endmodule

module module3;

    logic [Baz_pkg::ONE-1:0] x;

    module3A a();
    module3B b(x);

endmodule
