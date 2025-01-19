slang-netlist
=============

> **Warning**
>
> slang-netlist is a work in progress and may not work as expected. Check
> TODO.md for a list of some new features and fixes that are planned. If you
> encounter a problem, please submit a bug report via Issues.

slang-netlist is a library and tool for analysing the source-level static
connectivity of a design. This capability can be useful, for example, to
develop structural checks or to investigate timing paths, rather than having to
use synthesis to obtain a gate-level netlist.

Using the example of a simple adder:

```
module adder
  #(parameter p_width = 32)(
    input  logic [p_width-1:0] i_a,
    input  logic [p_width-1:0] i_b,
    output logic [p_width-1:0] o_sum,
    output logic               o_co
  );
  logic [p_width-1:0] sum;
  logic co;
  assign {co, sum} = i_a + i_b;
  assign o_sum = sum;
  assign o_co = co;
endmodule
```

The slang-netlist command-line tool can be used to trace paths through the
design, such as:

```
➜  slang-netlist adder.sv --from adder.i_a --to adder.o_sum -q
adder.sv:10:22: note: variable i_a read from
  assign {co, sum} = i_a + i_b;
                     ^~~

adder.sv:10:15: note: variable sum assigned to
  assign {co, sum} = i_a + i_b;
              ^~~

adder.sv:11:18: note: variable sum read from
  assign o_sum = sum;
                 ^~~

adder.sv:11:10: note: variable o_sum assigned to
  assign o_sum = sum;
         ^~~~~
```
