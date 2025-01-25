timeunit 1ns / 1ps;
timeprecision 1ps;

(* foo = 1 *) package static p;
    timeunit 1ns;
    program; endprogram
    export *::*;
endpackage

module automatic m1 import p::*; #(int i = 1)
    (a, b, , .c({a, b[0]}));
    input a;
    output [1:0] b;
endmodule

module m2 #(parameter i = 1, localparam j = i)
    (input int a[], (* bar = "asdf" *) output wire b = 1, ref c,
     interface.mod d, .e());
endmodule

extern interface I(input a, output b);

interface I(.*);
    modport mod(input a);
endinterface

extern macromodule m3;

macromodule m3;
    wire b;
    logic c;
    I d(.a(), .b());
    m2 m(, b, c, d, );

    $info("Hello %s", "world");

    wor [1:0] w = 1;
    assign (supply0, weak1) #(1:0:1, 2:1:0) w = 2;

    wor u,v;
    alias {u,v} = w;

    logic f;
    event ev;
    initial begin
        repeat (3) @(negedge b) f = #2 1;
        wait (f) ++f;
        wait fork;
        wait_order (m3.ev) f++;

        fork : fkb
            static int i = 1;
            disable fork;
        join_none

        disable m3.foo;

        if (1) begin end else begin end

        unique0 casex (w)
            0, 1: ;
            default ;
        endcase

        case (w) inside
            [0: 3]: ;
        endcase
    end

    always_ff @(posedge b iff f == 1) begin
        forever break;
        repeat (f + 2) continue;
        while (1)
            ;
        for (int i = 0, j = i; i < 10; i += 2, j += i) begin end
        foreach (w[q]) begin end
    end

    always @* begin : foo
    end : foo

    always_comb begin
        typedef union tagged {
            void Invalid;
            int Valid;
        } VInt;

        typedef union tagged {
            struct {
                bit [4:0] reg1, reg2, regd;
            } Add;
            union tagged {
                bit [9:0] JmpU;
                struct {
                    bit [1:0] cc;
                    bit [9:0] addr;
                } JmpC;
            } Jmp;
        } Instr;

        VInt v;
        Instr instr;
        automatic int rf[] = new [3];
        static longint pc = 'x;

        case (v) matches
            tagged Invalid &&& ~w : $display ("v is Invalid");
            tagged Valid .n : $display ("v is Valid with value %d", n);
        endcase

        case (instr) matches
            tagged Add .s: case (s) matches
                            '{.*, .*, 0} : ; // no op
                            '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                          endcase
            tagged Jmp .j: case (j) matches
                            tagged JmpU .a : pc = pc + a;
                            tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                           endcase
        endcase

        if (instr matches (tagged Jmp .j) &&&
            j matches (tagged JmpC '{cc:.c,addr:.a})) begin
            pc = c[0] & a[0];
            pc = instr matches (tagged Jmp .j) &&&
                  j matches (tagged JmpC '{cc:.c,addr:.a}) ? c[0] & a[0] : 0;
        end
        else begin
        end
    end

    always_latch begin
    end

    genvar j;
    for (genvar i = 0; i < 10; i += 2)
        if (i == 7) begin
        end

    ;

    generate
        case ($bits(w))
            0, 1: begin end
            2: begin end
            default: begin end
        endcase
    endgenerate

    assertion0: assert #0 (1 == 1) else $display("Hello!");
    assertion1: assume final (2 != 1) else $display("Hello!");

    if (1) begin
        logic a,b,c,d,e,f;

        property p1(x,y);
            ##1 x |-> y;
        endproperty

        wire clk;
        property p2;
            @(posedge clk)
            a ##1 (b || c)[->1] |->
                if (b)
                    p1(d,e)
                else
                    f;
        endproperty
        cover property (p2 and p2);
    end

    prim prim_inst(q, r);
    rcmos #1step (q, r, s, t);

    defparam m3.m.i = 1:1:1;

    clocking cb @(r or s);
        default input posedge #3ps;
        input a = t;
    endclocking

    global clocking cb2 @t; endclocking

    default clocking cb;
    default disable iff 1 dist { [1:2] :/ 3, 2 };

endmodule : m3

extern program p(a, b);

program p(a, b);
    input a, b;
endprogram : p

extern primitive prim(output reg a, input b);

primitive prim(output reg a, input b);
    table
        0 : ? : 1;
        1 : 0 : x;
    endtable
endprimitive

(* attr = 3.14 *) bind m3.m m1 #(1) bound('x, , , );

config cfg;
    localparam i = 1;
    design work.m3;
    default liblist a b;
    cell m3 use work.m3;
endconfig

module ALU (o1, i1, i2, opcode);
    input [7:0] i1, i2;
    input [2:1] opcode;
    output [7:0] o1;

    specify
        specparam s1 = 2;
        if (opcode == 2'b00) (i1,i2 *> o1) = (25.0, 25.0);
        if (opcode == 2'b01) (i1 => o1) = (5.6, 8.0);
        if (opcode == s1) (i2 => o1) = (5.6, 8.0);
        (opcode *> o1) = (6.1, 6.5);
    endspecify
endmodule

interface Iface;
    extern function void foo(int i, real r);
    extern forkjoin task t3();

    modport m(export foo, function void bar(int, logic), task baz, export func);
    modport n(import function void func(int), import task t2);
    modport o(export t2);
endinterface

module n(Iface.m a);
    initial begin
        a.foo(42, 3.14);
        a.bar(1, 1);
        a.baz();
    end

    function void a.bar(int i, logic l); endfunction
    task a.baz; endtask
    function void a.func(int i); endfunction

    function void a.foo(int i, real r);
    endfunction
endmodule

module m4;
    Iface i1();
    n n1(i1);

    Iface i2();
    n n2(i2.m);

    localparam int baz = 3;
    task i1.t2;
        static int i = baz;
    endtask

    task i2.t2;
        static int i = baz;
    endtask
endmodule

typedef enum { cover_none, cover_all } coverage_level;
checker assert_window1 (
    logic test_expr,
    untyped start_event,
    untyped end_event,
    event clock = $inferred_clock,
    logic reset = $inferred_disable,
    string error_msg = "violation",
    coverage_level clevel = cover_all
);
    default clocking @clock; endclocking
    default disable iff reset;
    bit window = 1'b0, next_window = 1'b1;
    rand bit q;

    always_comb begin
        if (reset || window && end_event)
            next_window = 1'b0;
        else if (!window && start_event)
            next_window = 1'b1;
        else
            next_window = window;
    end

    always_ff @clock
        window <= next_window;

    property p_window;
        start_event && !window |=> test_expr[+] ##0 end_event;
    endproperty

    a_window: assert property (p_window) else $error(error_msg);

    generate if (clevel != cover_none) begin : cover_b
        cover_window_open: cover property (start_event && !window)
        $display("window_open covered");
        cover_window: cover property (
            start_event && !window
            ##1 (!end_event && window) [*]
            ##1 end_event && window
        ) $display("window covered");
    end : cover_b
    endgenerate
endchecker : assert_window1

module m5;
    logic a, b;
    assert_window1 aw1(1 + 1, a, b);
endmodule

class C;
    int i;
    static int j;
    extern function int foo(int bar, int baz = 1);
endclass

class D;
    extern static function real foo;
endclass

localparam int k = 5;

function int C::foo(int bar, int baz = 1);
    i = j + k + bar + baz;
endfunction

function real D::foo;
endfunction

class G #(type T);
    extern function T foo;
endclass

function G::T G::foo;
    return 0;
endfunction

class H #(int p);
    extern function int foo;
endclass

function int H::foo;
endfunction

module m7;
    G #(real) g1;
    G #(int) g2;

    int i = g2.foo();
    real r = D::foo();
endmodule

class A;
    integer i = 1;
    integer j = 2;
    function integer f();
        f = i;
    endfunction
endclass

class B extends A;
    integer i = 2;
    function void f();
        i = j;
        super.i = super.j;
        j = super.f();
        j = this.super.f();
    endfunction
endclass

class C2 extends B;
    function void g();
        f();
        i = j + C::j + A::f();
    endfunction

    rand bit [63:0] value;
    rand logic q;
    constraint value_c {
        value[63] dist {0 :/ 70, 1 :/ 30};
        value[0] == 1'b0;
        value[15:8] inside {
            8'h0,
            8'hF
        };
        solve value before q;
        soft value[3:1] > 1;
        q -> { value[4] == 0; }
        if (q) { foreach (value[b]) { value[b] == 0; } } else { disable soft value; }
    }
endclass

module m6;
    A a = new;
    A b1 = B::new;
    B b2 = new;
    C2 c = new;
    int depth;
    integer i = b1.f();
    initial begin
        b2.f();
        a = b2;
        c.i = c.j;

        randsequence(main)
            main : first second;
            first : add | dec := (1 + 1);
            second : repeat($urandom_range(2, 6)) first;
            add : if (depth < 2) first else second;
            dec : case (depth & 7)
                0 : add;
                1, 2 : dec;
                default : first;
            endcase;
            third : rand join first second;
            fourth(string s = "done") : { if (depth) break; };
        endsequence
    end
endmodule

class C3;
    enum {red, green, blue} color;
    bit [3:0] pixel_adr, pixel_offset, pixel_hue;
    logic clk, x, y, c;

    covergroup g2 (string instComment) @(posedge clk);
        Offset: coverpoint pixel_offset;
        Hue: coverpoint pixel_hue;
        AxC: cross color, pixel_adr;
        all: cross color, Hue, Offset;

        option.comment = instComment;

        e: coverpoint x iff (clk) {
            option.weight = 2;
            wildcard bins a = { [0:63],65 };
            bins b[] = { [127:150],[148:191] }; // note overlapping values
            bins c[] = { 200,201,202 };
            bins d = { [1000:$] };
            bins others[] = default;

            bins sa = (4 => 5 => 6), ([7:9],10 => 11,12);
            bins sb[] = (12 => 3 [* 1]);
            bins sc = (12 => 3 [-> 1]);
            bins sd = (12 => 3 [= 1:2]);
        }
        cross e, y {
            option.weight = c;
            bins one = '{ '{1,2}, '{3,4}, '{5,6} };
            ignore_bins others = (!binsof(e.a) || !binsof(y) intersect {1}) with (e > 10);
        }
        b: cross y, x;
    endgroup
endclass

module m9;
    logic [3:0] a = {4 {1'b1}};
endmodule

module m10;
    byte stream[$];
    class Packet;
        rand int header;
        rand int len;
        rand byte payload[];
        int crc;
        constraint G { len > 1; payload.size == len ; }
        function void post_randomize; crc = payload.sum; endfunction
    endclass

    initial begin
        byte q[$];
        automatic Packet p = new;
        {<< byte{ p.header, p.len, p.payload with [0 +: p.len], p.crc }} = stream;
        stream = stream[ $bits(p) / 8 : $ ];
    end
endmodule
