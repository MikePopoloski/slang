module Foo #(parameter int foo = 4, bar = foo + 1, baz = bar * 4)();

endmodule

module Bar();

    Foo f();
    Foo #(.foo(2)) g();

endmodule
