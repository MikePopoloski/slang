timeunit 1ns / 1ps;
timeprecision 1ps;

(* foo = 1 *) package static p;
    timeunit 1ns;
    parameter int x = 1;
    parameter type y_t = logic[x:0];
    program; endprogram
    export *::*;
endpackage

package pack2;
    import p::x;
    export p::x;
endpackage

module automatic m1 import p::*, p::x; #(int i = 1)
    (a, b, , .c({a, b[0]}));
    input a;
    output [1:0] b;
endmodule

module m2 #(
    parameter i = 1,
    localparam j = i,
    parameter type x_t = bit
)
    (input int a[], (* bar = "asdf" *) output logic b = 1, ref c,
     interface.mod d, .e());
endmodule

extern interface I(input a, output b);

interface I(.*);
    modport mod(input a);
endinterface

extern macromodule m3;

extern primitive EP(output a, input b);

primitive EP(.*);
    table 0 : 1; endtable
endprimitive

macromodule m3;
    wire b;
    logic c;
    I d(.a(), .b());

    typedef p::y_t y_t;

    m2 #(
        .x_t(y_t)
    ) m (, b, c, d, );


    $info("Hello %s", "world");

    wor [1:0] w = 1;
    assign (supply0, weak1) #(1:0:1, 2:1:0) w = 2;

    wor u,v;
    alias {u,v} = w;

    logic f, z;
    event ev;
    initial begin
        byte q, r, x;

        repeat (3) @(negedge b) f = #2 1;
        wait (f) ++f;
        wait fork;
        wait_order (m3.ev) f++;

        fork : fkb
            static int i = 1;
            disable fork;
        join_none

        disable m3.foo;

        assign z = 1;
        deassign z;

        force z = 1;
        release z;

        if (1) begin end else begin end

        unique0 casex (w)
            0, 1: ;
            default ;
        endcase

        case (w) inside
            [0: 3]: ;
        endcase

        randcase
            q + r : x = 1;
            q - r : x = 2;
            q ^ ~r : x = 3;
            12'h800 : x = 4;
        endcase

        f <= #1step 1;
        f <= repeat(3) @(ev) 1;
    end

    logic ww[3][2];

    always_ff @(posedge b iff f == 1) begin
        forever break;
        repeat (f + 2) continue;
        while (1)
            ;
        for (int i = 0, j = i; i < 10; i += 2, j += i) begin end
        foreach (w[q]) begin end
        foreach (ww[,]) begin end
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
        Instr instr = tagged Add '{reg1:0, reg2:1, regd:3};
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
        do -> ev; while (~b);
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
    cover (2 != 1);

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

        property p3(s);
            int r;
            @(posedge clk) strong((a, r = 1) intersect first_match(b, r = 2))
                and not sync_accept_on(c)
                    case (e)
                        2'd0 : a && b;
                        2'd1 : a ##2 b;
                        2'd2 : a ##4 b;
                        2'd3 : a ##8 b;
                        default: 1;
                    endcase
                or (a throughout b or c) implies (a iff always[1:2] b
                until a s_until b s_until_with a until_with b);

        endproperty

        property p4(property parg, sequence sarg);
            parg and sarg;
        endproperty

        assume property (p3(d));
        assume property (p2);
        cover property (disable iff (~clk) p3(d) and p2);
        cover sequence (a within b);
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
    default disable iff 1 dist { [1:2] :/ 3, 2, default :/ 4 };

    int zz;
    wire clk2;
    event ev3;
    initial begin
        ##(5 + 2) zz <= 1;

        ->> ev3;

        expect (@(posedge clk2) f #-# zz);
        restrict property (@(posedge clk2) f #-# zz);
    end

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

primitive srff (q, s, r);
    output q; reg q;
    input s, r;
    initial q = 1'b1;
    table
        (10) 0 : ? : 1 ;
    endtable
endprimitive

(* attr = 3.14 *) bind m3.m m1 #(1) bound('x, , , );
bind m2 :m3.m m1 #(2) bound2('x, , , );

config cfg;
    localparam i = 1;
    design work.m3;
    default liblist a b;
    cell m3 use work.m3;
    instance m17.j liblist a;
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
        (posedge i2 => (o1 +: i1)) = (10, 8);
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
    logic a, b, c, d, e, clk;

    default clocking @(posedge clk); endclocking

    assert_window1 aw1(1 + 1, a, b);

    initial begin
        assert_window1 aw2(1 + 1, a, b);
    end

    sequence abc;
        @(posedge clk) a ##1 b ##1 c;
    endsequence

    sequence de;
        @(negedge clk) d ##[2:5] e;
    endsequence

    program check;
        initial begin
            wait( abc.triggered || de.triggered );
            if( abc.triggered )
                $display( "abc succeeded" );
            if( de.triggered )
                $display( "de succeeded" );
        end
    endprogram
endmodule

class C;
    int i = 5ns;
    static int j;
    extern function int foo(int bar, int baz = 1);
endclass

class D;
    extern static function real foo;
endclass

localparam int k = 5;

function int C::foo(int bar, int baz = 1);
    i = j + longint'(k) + bar + baz;
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
    rand logic q, r;
    constraint value_c {
        value[63] dist {0 :/ 70, 1 :/ 30};
        value[0] == 1'b0;
        value[15:8] inside {
            8'h0,
            8'hF
        };
        unique { q, r };
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
    C2 c = null;
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
    logic arr[3];

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

            bins se = e with (item % 3 == 0);
            bins sf = arr;
        }
        X: cross e, y {
            option.weight = c;
            bins one = '{ '{1,2}, '{3,4}, '{5,6} };
            bins two = X with (e < 257) matches 127;
            ignore_bins others = (!binsof(e.a) || !binsof(y) intersect {1}) with (e > 10);
        }
        b: cross y, x;
    endgroup

    function new;
        g2 = new("SDF");
    endfunction

    function foo;
        return 0;
    endfunction

    covergroup g3 @@(begin foo or end foo);
    endgroup

    covergroup g4 with function sample();
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
        automatic Packet p2 = new p;
        {<< byte{ p.header, p.len, p.payload with [0 +: p.len], p.crc }} = stream;
        stream = stream[ $bits(p) / 8 : $ ];
    end
endmodule

module m11(input clk);
    int a[4] = '{default: 1};
    int b[] = '{3 {1}};
    int c = $bits(int);
    localparam type T = type(b);

    initial begin
        if (type(b) == type(a) && $rose(c, @(posedge clk))) begin
            $display("SDF");
        end
    end
endmodule

int unitVar;

module m12;
    int i, j, k;
    int a[];
    time t;
    shortreal sr;
    shortint si;
    int qq[$:3];
    final begin
        i = j + k;
        i = j - k;
        i = j * k;
        i = j / k;
        i = j % k;
        i = j | k;
        i = j & k;
        i = j ^ k;
        i = j ** k;
        i = j ^~ k;
        i = j << k;
        i = j <<< k;
        i = j >> k;
        i = j >>> k;
        i = j -> k;
        i = j <-> k;
        i += j;
        i -= j;
        i *= j;
        i /= j;
        i %= k;
        i &= k;
        i |= k;
        i ^= k;
        i <<= j;
        i <<<= j;
        i >>= j;
        i >>>= j;
        i = j === k;
        i = j !== k;
        i = j ==? k;
        i = j !=? k;
        i = j > k;
        i = j >= k;
        i = j < k;
        i = j <= k;
        i = +j;
        i = -j;
        i = !j;
        i = ~j;
        i = &j;
        i = ~&j;
        i = |j;
        i = ~|j;
        i = ^j;
        i = ~^j;
        i = ^~j;
        ++i;
        i++;
        --i;
        i--;
        i = signed'(j);
        i = a.or;
        i = a.and;
        i = a.xor;
        i = a.unique()[0];
        i = j[0];
        i = j[3:2];
        i = j[3-:1];
        i = $unit::unitVar;
        i = $root.m12.j;
        a = {};
        void'(a.find(x) with (x > 5).unique);
    end
endmodule

module m13;
    struct packed {
        int a;
        logic b;
    } x;

    union packed {
        logic a;
        bit b;
    } y;

    chandle z;

    realtime w[*];

    typedef real TR[5];
    nettype TR wTR;

    wTR #1 udfntwd;

    typedef class Base;

    class Base #(parameter p = 1);
        typedef struct {
            real r;
            bit[p-1:0] data;
        } T;

        static function T Tsum (input T driver[]);
            Tsum.r = 0.0;
            Tsum.data = 0;
            foreach (driver[i])
                Tsum.data += driver[i].data;
            Tsum.r = $itor(Tsum.data);
        endfunction
    endclass

    typedef Base#(32) MyBaseT;
    nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;

    typedef Base#(64) MyBaseType;
    nettype MyBaseType::T wideTsum with MyBaseType::Tsum;

    narrowTsum net1; // data is 32 bits wide
    wideTsum net2; // data is 64 bits wide
endmodule

module m14(input a, output b);
    specify
        pulsestyle_onevent b, b;
        pulsestyle_ondetect b;
        showcancelled b;
        noshowcancelled b, b;
        ifnone (a => b) = (1, 0);
    endspecify

    m13 instArr[3:1][2:5]();

    (* maybe_unknown *) unknowninst ui(1, 2);

    let eq(x, y = b) = x == y;
endmodule

module m15(input a, clk, data, output b);
    reg notify;
    wire bar;
    wire [1:0] w;

    specify
        specparam tSU = 1, tHLD = 3:4:5;
        $setup(posedge clk &&& a, data, 42);
        $hold(posedge clk, data, 42, );
        $setuphold(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, dclk, ddata);
        $recovery(posedge clk, data, 42);
        $removal(posedge clk, data, 42, );
        $recrem(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, dclk);
        $recrem(posedge clk, data, tSU, tHLD, notify, 0:1:0, bar, w[0], ddata);
        $skew(posedge clk, data, 42);
        $timeskew(posedge clk, negedge data, 42, , 1, 0:1:0);
        $fullskew(posedge clk, negedge data, 42, 32, , 1, 0:1:0);
        $period(edge [01, x1, 1Z] clk, 42, notify);
        $width(posedge clk, 42, 52);
        $nochange(posedge clk, negedge data, -1, -2);
    endspecify

    wire x = dclk;
    wire y = ~ddata;
endmodule

module m16(input wire clk, data, output reg b);
    logic dclk, ddata;
    specify
        $recrem(posedge clk, data, 1, 2, , , , dclk, );
    endspecify

    function void func(int a = 1, b = 2);
    endfunction

    initial begin
        func(,);
        func(.a(1), .b(2));
    end
endmodule

import "DPI-C" context \begin = function void dpi_f1(input, output logic[]);

function dpi_e1; endfunction
export "DPI-C" function dpi_e1;

interface J(wire clk);
    interface I(input int q);
        clocking cb @(posedge clk);
        endclocking

        int a, b;
        modport m(input .i({a, q, b}));
        modport n(input b, clocking cb);

        struct { int i; } s;
        modport o(input .q(s.i));
    endinterface

    I i(3);
endinterface

module m17;
    wire clk;
    J j(.*);

    virtual interface J jvi = j;

    trireg (large) logic #(0,0,0) cap1;
    pullup (strong1) p1 (neta), p2 (netb);

    class C;
        rand integer x;
    endclass
    function int F(C obj, integer x);
        F = obj.randomize() with { x < local::x; };
    endfunction
endmodule

class Base;
    string name;
    local int m_id;
    function new(string name, output int id);
        this.name = name;
        id = m_id++;
    endfunction : new
endclass : Base

interface class IfaceClass;
endclass

class B2 extends Base implements IfaceClass;
    int size;
    function new(int size, default);
        super.new(default); // Optional explicit use of super.new
        this.size = size;
    endfunction : new
endclass : B2

class B3 extends Base(default);
    function :final foo(); endfunction

    constraint co;
endclass : B3
