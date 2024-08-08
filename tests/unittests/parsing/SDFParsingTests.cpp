// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"

TEST_CASE("SDF file correct (unformatted and with comments") {
    auto& text = R"(
(DELAYFILE
 (SDFVERSION "3.0")
 (DESIGN "mux")
 (DATE "Fri Apr 19 09:40:01 2019")
 (VENDOR "Xilinx")
 (PROGRAM "Xilinx SDF Writer")
 (VERSION "P.20131013")
 (DIVIDER /)
 //(VOLTAGE 1.800::1.800)
 (VOLTAGE 1:-1.0e-10:-1.2)
 (PROCESS "1.000::1.000")
 (TEMPERATURE 25.000::25.000)
 (TIMESCALE 100.0 ps)
 (CELL (CELLTYPE "X_BUF")
  //(INSTANCE aa/aa.das/a)
  (INSTANCE aa/aa/das/a)
  (DELAY (PATHPULSE a y (13) (24))
   (PATHPULSE b y (15) (21))
   (PATHPULSEPERCENT a y (13) (24))
   (PATHPULSEPERCENT b y (15) (21))
  )
 )
    (CELL (CELLTYPE "X_BUF")
     (INSTANCE a27_IBUF)
     //    (DELAY)
    )
    (CELL (CELLTYPE "X_BUF")
     (INSTANCE a27_IBUF)
     (DELAY
      (ABSOLUTE
       (IOPATH (posedge I) O/sadas/df (RETAIN (4:5:7) (5:6:9) (3)) ( 1500 )( 1500 ))
       (COND ~a (IOPATH b y (0.37) (0.45) ) )
       (COND aa/b/b/n /*? {fsafas} : {fdsafas}*/ (IOPATH b y (0.37) (0.45) ) )
       (COND 0 (IOPATH b y (0.37) (0.45) ) )
       (COND B2 (IOPATH b y (0.37) (0.45) ) )
       (COND B0 (IOPATH b y (0.37) (0.45) ) )
       (COND 1 B0 (IOPATH b y (0.37) (0.45) ) )
       (COND aa/b/b/n ? {(sdsadsasdas) ? {fsafas, fasfas, 1 B0} : fdsafas} : {asds, asdsa} (IOPATH b y (0.37) (0.45) ) )
       //(COND aa/b/b/n ? {sdsadsasdas ? {fsafas[2], fasfas, 1 B0} : fdsafas} : {asds, asdsa} (IOPATH b y (0.37) (0.45) ) )
       //(COND aa/b/b/n ? {sdsadsa + sdas ? {fsafas, fasfas, 2b1} : fdsafas} : {asds, asdsa} (IOPATH b y (0.37) (0.45) ) )
       //(COND "asadas" ~a/a/a/a/a[2:3] (IOPATH b y (0.37) (0.45) ) )
      )
     )
     (TIMINGCHECK(
     SETUP din (posedge clk) (3:4:5.5))
     (HOLD din (posedge clk) (4:5.5:7))
      (SETUPHOLD (COND reset din) (posedge clk) (12) (9.5))
      (SETUPHOLD (COND ~reset din) (posedge clk) (12) (9.5))
      //(SETUPHOLD (COND +reset din) (posedge clk) (12) (9.5))
      //(SETUPHOLD (COND (reset) din) (posedge clk) (12) (9.5))
      //(SETUPHOLD (COND reset[2] din) (posedge clk) (12) (9.5))
      //(SETUPHOLD (posedge clk) (12) (9.5) (SCOND reset))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset -> reset))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == reset))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (COND reset == reset))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (CCOND reset == reset))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset[4] == reset))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == reset[4]))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset[3] == reset[4]))
      (SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset[4] == reset[4]))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset[4] == reset[4:3]))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == reset[+4]))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == reset[-4]))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == reset[+4]))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND reset == !reset))
      //(SETUPHOLD (posedge clk) (negedge clk1) (12) (9.5) (SCOND !reset == reset))
(SETUPHOLD din (posedge clk) (12) (9.5) (CCOND ~reset))
(RECOVERY (posedge clearbar) (posedge clk) (11.5))
(REMOVAL (posedge clearbar) (posedge clk) (6.3))
(REMOVAL (posedge clearbar) (posedge clk) (6.3))
(SKEW (posedge clk1) (posedge clk2) (6))
(BIDIRECTSKEW (posedge clk1) (posedge clk2) (6) (7))
(WIDTH (posedge clk) (30))
(WIDTH (negedge clk) (16.5))
(PERIOD (posedge clk) (46.5))
(NOCHANGE (negedge write) addr (4.5) (3.5))
     )
     (LABEL
      (ABSOLUTE
       (TCLK_Q (7.54:12.14:19.78) (6.97:13.66:18.47))
       (TCLK_QB (8.16:13.74:20.25) (7.63:14.83:21.42))
       (TSETUP_D_CLK (3:4:5.6))
       (THOLD_D_CLK (4:5.6:7))
      ))
     (TIMINGENV
      (PATHCONSTRAINT I2/H01 I1/N01 (989:1269:1269) (989:1269:1269) )
      //(PATHCONSTRAINT I2/H01 /*I3.N01*/ (904:1087:1087) (904:1087:1087) )
     )
     (TIMINGENV
     (PATHCONSTRAINT y/z/i3 y/z/o2 a/b/o1 (25.1) (15.6))
     (PERIODCONSTRAINT bufa/y (10)
     (EXCEPTION (INSTANCE dff3) (INSTANCE ddasdas32) )
     )
     (SUM (m/n/o1 y/z/i1) (y/z/o2 a/b/i2) (67.3))
     (DIFF (m/n/o1 y/z/i1) (y/z/o2 a/b/i2) (67.3))
     (SKEWCONSTRAINT (posedge y) (7.5))
     (ARRIVAL (posedge MCLK) D[15:0] (10) (40) (12) (45) )
     (ARRIVAL (posedge MCLK) D[0] (10) (40) (12) (45) )
     (DEPARTURE (posedge SCLK) A[15:0] (8) (20) (12) (34) )
     (SLACK B (3) (3) (7) (7))
     (WAVEFORM clka 15 (posedge 0 2) (negedge 5 7))
     (WAVEFORM clkb 25
     (negedge 0) (posedge 5)
     (negedge 10) (posedge 15)
     )
     (WAVEFORM clkb 50
     (negedge -10) (posedge 20)
     )
     //(WAVEFORM clka -15 (posedge 0 2) (negedge 5 7))
     )
    )

    )
    /*(DELAYFILE
      (SDFVERSION "3.0")
      (DESIGN "mux")
      (DATE "Fri Apr 19 09:40:01 2019")
      (VENDOR "Xilinx")
      (PROGRAM "Xilinx SDF Writer")
      (VERSION "P.20131013")
      (DIVIDER /)
    //(VOLTAGE 1.800::1.800)
    (VOLTAGE 1:-1.0e-10:-1.2)
    (PROCESS "1.000::1.000")
    (TEMPERATURE 25.000::25.000)
    (TIMESCALE 100.0 ps)
    )*/
)";

    auto& unit = parseSDFUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(unit.kind == SyntaxKind::SDFUnit);
    REQUIRE(unit.members.size() == 1);
    REQUIRE(unit.members[0]->kind == SyntaxKind::SDFDelayFile);
}

TEST_CASE("correct SDF simple file") {
    auto& text = R"(
(DELAYFILE
  (SDFVERSION "3.0")
  (DESIGN "mux")
  (DATE "Fri Apr 19 09:40:01 2019")
  (VENDOR "Xilinx")
  (PROGRAM "Xilinx SDF Writer")
  (VERSION "P.20131013")
  (DIVIDER /)
  (VOLTAGE 1.800::1.800)
  (PROCESS "1.000::1.000")
  (TEMPERATURE 25.000::25.000)
  (TIMESCALE 1ns)
  (CELL (CELLTYPE "X_BUF")
    (INSTANCE a27_IBUF)
      (DELAY
        (ABSOLUTE
          (IOPATH I O ( 1500 )( 1500 ))
        )
      )
    (DELAY
     (ABSOLUTE
      (INTERCONNECT wb_clk_i clkbuf_0_wb_clk_i.A (0.036:0.036:0.036) (0.035:0.035:0.035))
      (INTERCONNECT wb_clk_i ANTENNA_1.DIODE (0.036:0.036:0.036) (0.035:0.035:0.035))
      (INTERCONNECT wb_rst_i input10.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[8] input9.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[7] input8.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[6] input7.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[5] input6.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[4] input5.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[3] input4.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[2] input3.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[1] input2.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT io_in[0] input1.A (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT _135_O/Y _248_/A1 (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT _135_O/Y _249_/A1 (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT _136_O/Y _248_/B2 (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT _136_O/Y _249_/B2 (0.000:0.000:0.000) (0.000:0.000:0.000))
      (INTERCONNECT _298_.Q ANTENNA_hold54_A.DIODE (0.031:0.031:0.031) (0.030:0.030:0.030))
     )
    )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE DSACK0_OBUF_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_AND3")
    (INSTANCE DSACK0_OBUF_D2_PT_0)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 2900 )( 2900 ))
          (PORT I1 ( 2900 )( 2900 ))
          (PORT I2 ( 2900 )( 2900 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_BUF")
    (INSTANCE cntr_0_Q)
      (DELAY
        (ABSOLUTE
          (IOPATH I O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_OR2")
    (INSTANCE cntr_0_tsimcreated_prld_Q)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_FF")
    (INSTANCE cntr_0_REG)
      (DELAY
        (ABSOLUTE
          (IOPATH CLK O ( 400 )( 400 ))
          (IOPATH SET O ( 6000 )( 6000 ))
          (IOPATH RST O ( 6000 )( 6000 ))
        )
      )
      (TIMINGCHECK
        (SETUPHOLD (posedge I) (posedge CLK) (2300)(1400))
        (SETUPHOLD (negedge I) (posedge CLK) (2300)(1400))
        (SETUPHOLD (posedge CE) (posedge CLK) (0)(0))
        (PERIOD (posedge CLK) (5600))
        (WIDTH (posedge SET) (5000))
        (WIDTH (posedge RST) (5000))
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE cntr_0_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_AND2")
    (INSTANCE cntr_0_RSTF)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 2900 )( 2900 ))
          (PORT I1 ( 2900 )( 2900 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_BUF")
    (INSTANCE cntr_1_Q)
      (DELAY
        (ABSOLUTE
          (IOPATH I O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE cntr_1_tsimcreated_xor_Q)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 1400 )( 1400 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_FF")
    (INSTANCE cntr_1_REG)
      (DELAY
        (ABSOLUTE
          (IOPATH CLK O ( 400 )( 400 ))
          (IOPATH SET O ( 6000 )( 6000 ))
          (IOPATH RST O ( 6000 )( 6000 ))
        )
      )
      (TIMINGCHECK
        (SETUPHOLD (posedge I) (posedge CLK) (2300)(1400))
        (SETUPHOLD (negedge I) (posedge CLK) (2300)(1400))
        (SETUPHOLD (posedge CE) (posedge CLK) (0)(0))
        (PERIOD (posedge CLK) (5600))
        (WIDTH (posedge SET) (5000))
        (WIDTH (posedge RST) (5000))
      )
  )
  (CELL (CELLTYPE "X_AND2")
    (INSTANCE cntr_1_RSTF)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 2900 )( 2900 ))
          (PORT I1 ( 2900 )( 2900 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_OR3")
    (INSTANCE ETHRNT_OBUF_D2)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (PORT I2 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE FLOPPY_OBUF_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_AND7")
    (INSTANCE FLOPPY_OBUF_D2_PT_0)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 1000 )( 1000 ))
          (PORT I1 ( 1000 )( 1000 ))
          (PORT I2 ( 1000 )( 1000 ))
          (PORT I3 ( 1000 )( 1000 ))
          (PORT I4 ( 1000 )( 1000 ))
          (PORT I5 ( 1000 )( 1000 ))
          (PORT I6 ( 1000 )( 1000 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
          (IOPATH I3 O ( 0 )( 0 ))
          (IOPATH I4 O ( 0 )( 0 ))
          (IOPATH I5 O ( 0 )( 0 ))
          (IOPATH I6 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_OR3")
    (INSTANCE FLOPPY_OBUF_D2)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (PORT I2 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_BUF")
    (INSTANCE IDE_OBUF_Q)
      (DELAY
        (ABSOLUTE
          (IOPATH I O ( 500 )( 500 ))
        )
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE IDE_OBUF_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_AND7")
    (INSTANCE IDE_OBUF_D2_PT_0)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 1000 )( 1000 ))
          (PORT I1 ( 1000 )( 1000 ))
          (PORT I2 ( 1000 )( 1000 ))
          (PORT I3 ( 1000 )( 1000 ))
          (PORT I4 ( 1000 )( 1000 ))
          (PORT I5 ( 1000 )( 1000 ))
          (PORT I6 ( 1000 )( 1000 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
          (IOPATH I3 O ( 0 )( 0 ))
          (IOPATH I4 O ( 0 )( 0 ))
          (IOPATH I5 O ( 0 )( 0 ))
          (IOPATH I6 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_OR3")
    (INSTANCE IDE_OBUF_D2)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (PORT I2 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
          (IOPATH I2 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_AND2")
    (INSTANCE READ_n_OBUF_D2)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 1000 )( 1000 ))
          (PORT I1 ( 1000 )( 1000 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE I_MEMW_OBUF_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
  (CELL (CELLTYPE "X_XOR2")
    (INSTANCE cntr_2_cntr_2_RSTF_INT_D)
      (DELAY
        (ABSOLUTE
          (PORT I0 ( 0 )( 0 ))
          (PORT I1 ( 0 )( 0 ))
          (IOPATH I0 O ( 0 )( 0 ))
          (IOPATH I1 O ( 0 )( 0 ))
        )
      )
  )
)
)";

    auto& unit = parseSDFUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(unit.kind == SyntaxKind::SDFUnit);
    REQUIRE(unit.members.size() == 1);
    REQUIRE(unit.members[0]->kind == SyntaxKind::SDFDelayFile);
}

TEST_CASE("SDF file incorrect (invalid order of SDF file attributes/invalid number of SDFDelayFile "
          "members/no specified cells)") {
    auto& text = R"(
(DELAYFILE
  (SDFVERSION "3.0")
  (DESIGN "mux")
  (DATE "Fri Apr 19 09:40:01 2019")
  (VENDOR "Xilinx")
  (PROGRAM "Xilinx SDF Writer")
  (VERSION "P.20131013")
  (DIVIDER +)
  (PROCESS "1.000::1.000")
  (TEMPERATURE 25.000::25.000)
  (VOLTAGE 1.800::1.800)
  (TIMESCALE 1ns)
)

(DELAYFILE)
)";
    auto& unit = parseSDFUnit(text);

    REQUIRE(diagnostics.size() == 6);
    CHECK(diagnostics[0].code == diag::ExpectedSDFDivider);
    CHECK(diagnostics[1].code == diag::ExpectedSDFMember);
    CHECK(diagnostics[2].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[3].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[4].code == diag::ExpectedSDFMember);
    CHECK(diagnostics[5].code == diag::MemberLimitViolation);
}

TEST_CASE("SDF file incorrect (invalid timing check values)") {
    auto& text = R"(
(DELAYFILE
  (SDFVERSION "3.0")
  (DESIGN "mux")
  (DATE "Fri Apr 19 09:40:01 2019")
  (VENDOR "Xilinx")
  (PROGRAM "Xilinx SDF Writer")
  (VERSION "P.20131013")
  (VOLTAGE 1.800::1.800)
  (PROCESS "1.000::1.000")
  (TEMPERATURE 25.000::25.000)
  (TIMESCALE 1ns)
  (CELL
   (CELLTYPE "sky130_fd_sc_hd__dfrtp_1")
   (INSTANCE _279_)
   (DELAY
    (ABSOLUTE
     (IOPATH CLK Q (0.341:0.341:0.341) (0.379:0.379:0.379))
     (IOPATH RESET_B.d Q () (0.000:0.000:0.000))
    )
   )
   (TIMINGCHECK
     (REMOVAL (posedge RESET_B) (posedge CLK) (0.348:0.348:0.348))
     (RECOVERY (posedge RESET_B) (posedge CLK) (-0.255:-0.255:-0.255))
     (HOLD (posedge D) (posedge CLK) (-0.029:-0.030:-0.030))
     (HOLD (negedge D) (posedge CLK) (-0.020:-0.020:-0.021))
     (SETUP (posedge D) (posedge CLK) (0.054:0.054:0.055))
     (SETUP (negedge D) (posedge CLK) (0.088:0.088:0.089))
   )
  )
)
)";
    auto& unit = parseSDFUnit(text);

    REQUIRE(diagnostics.size() == 7);
    CHECK(diagnostics[0].code == diag::InvalidSDFValueExpr);
    CHECK(diagnostics[1].code == diag::ExpectedToken);
    CHECK(diagnostics[2].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[3].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[4].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[5].code == diag::UnexpectedEndDelim);
    CHECK(diagnostics[6].code == diag::UnexpectedEndDelim);
}
