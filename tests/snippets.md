These are snippets of code that I've run into that cause problems for other
tools and should probably get coverage in slang at some point. It's not always
clear from the spec how they ought to behave.


```
module m(a);
  output signed a;

  struct packed { logic[2:0] f; } a;

  initial begin
    a = 3'b100;
    $display(a > 0);
  end

endmodule
```

```
module m;
  logic [1:4] foo = 4'b0101;
  logic [0:1] a = 1;
  initial $display("%d", $left(foo[a+:2]));
endmodule
```

```
module n({a, b});
  ref logic a;
  input wire b;
endmodule

module m;
  logic [1:0] a;

  n n1(a);
endmodule
```