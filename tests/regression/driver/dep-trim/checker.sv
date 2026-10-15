// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
checker myChecker(logic a, event clk);
    assert property (@clk a);
endchecker
