#!/usr/bin/env python
# Takes an input text file containing the SystemVerilog language grammar
# and converts it to nice linked markdown.
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import os
import re

ourdir = os.path.dirname(os.path.realpath(__file__))

inf = open(os.path.join(ourdir, "grammar.txt"))
outf = open(os.path.join(ourdir, "../docs/grammar.md"), "w")

outf.write("# SystemVerilog\n")


def entry(line):
    match = re.match(r"(\w+) ::=", line)
    if match:
        s = match.group(1)
        outf.write('<a name="{}"></a>{} ::='.format(s, s.replace("_", "\\_")))
        line = line[len(match.group(0)) :]
    else:
        outf.write("&nbsp;&nbsp;&nbsp;&nbsp;")

    saved_match = None
    match = re.search(r"(\w+) ::=", line)
    if match:
        saved_match = line[match.start() :]
        line = line[: match.start()]

    def replacer(m):
        s = m.group(1)
        t = s
        for c in ["*", "-", "|", "[", "{", "_"]:
            t = t.replace(c, "\\" + c)
        if s not in ["|", "[", "]", "{", "}"]:
            return "`{}`".format(s)
        return t

    line = line.replace("{,", "{ ,")
    line = re.sub(r"([^\w\s]+)", replacer, line)
    line = re.sub(r"(\w+)", r"[\1](#\1)", line)
    outf.write(line + "  \n")

    if saved_match:
        entry(saved_match)


for line in inf:
    line = line.strip()
    if not line:
        continue

    if line.startswith("A."):
        count = line.split(" ")[0].count(".")
        if count == 1:
            outf.write("## ")
        elif count == 2:
            outf.write("### ")
        elif count == 3:
            outf.write("#### ")
        else:
            raise Exception("wut")
        outf.write(line + "\n")
    else:
        entry(line)
