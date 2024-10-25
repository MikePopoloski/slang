#!/usr/bin/env python
# This script generates C++ code for compiler diagnostics.
#
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT

import argparse
import os
import shlex
import subprocess
import sys


def writefile(path, contents):
    try:
        with open(path, "r") as f:
            existing = f.read()
    except OSError:
        existing = ""

    if existing != contents:
        with open(path, "w") as f:
            f.write(contents)


def main():
    parser = argparse.ArgumentParser(description="Diagnostic source generator")
    parser.add_argument("--outDir", default=os.getcwd(), help="Output directory")
    parser.add_argument("--srcDir", help="Source directory to search for usages")
    parser.add_argument("--incDir", help="Include directory to search for usages")
    parser.add_argument("--docs", action="store_true")
    parser.add_argument("--diagnostics", help="path to diagnostics file")
    parser.add_argument("--slangBin")
    args = parser.parse_args()

    inf = open(args.diagnostics)
    headerdir = os.path.join(args.outDir, "slang", "diagnostics")
    os.makedirs(headerdir, exist_ok=True)

    diags = {}
    groups = []
    diaglist = []
    subsystem = "General"
    curgroup = None

    def parsegroup(elems):
        nonlocal curgroup
        for e in elems:
            if e == "}":
                groups.append(curgroup)
                curgroup = None
                break
            curgroup[1].append(e)

    for line in [x.strip("\n") for x in inf]:
        if not line or line.startswith("//"):
            continue

        parts = shlex.split(line)
        if curgroup:
            parsegroup(parts)
        elif parts[0] == "subsystem":
            subsystem = parts[1]
            if subsystem not in diags:
                diags[subsystem] = []
        elif parts[0] == "group":
            curgroup = (parts[1], [])
            assert parts[2] == "="
            assert parts[3] == "{"
            parsegroup(parts[4:])
        else:
            sev = parts[0]
            if sev == "warning":
                diags[subsystem].append(("Warning", parts[2], parts[3], parts[1]))
                diaglist.append(parts[2])
            elif sev == "error":
                diags[subsystem].append(("Error", parts[1], parts[2], ""))
                diaglist.append(parts[1])
            elif sev == "note":
                diags[subsystem].append(("Note", parts[1], parts[2], ""))
                diaglist.append(parts[1])
            else:
                raise Exception("Invalid entry: {}".format(line))

    if args.docs:
        createdocs(
            args.outDir,
            os.path.join(os.path.dirname(args.diagnostics), "warning_docs.txt"),
            args.slangBin,
            diags,
            groups,
        )
    else:
        for k, v in sorted(diags.items()):
            createheader(os.path.join(headerdir, k + "Diags.h"), k, v)

        createsource(os.path.join(args.outDir, "DiagCode.cpp"), diags, groups)
        createallheader(os.path.join(headerdir, "AllDiags.h"), diags)

        doCheck = False
        if doCheck:
            diaglist = checkDiags(args.srcDir, diaglist)
            diaglist = checkDiags(args.incDir, diaglist)
            reportUnused(diaglist)


def createheader(path, subsys, diags):
    output = """//------------------------------------------------------------------------------
//! @file {}Diags.h
//! @brief Generated diagnostic enums for the {} subsystem
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"

namespace slang::diag {{

""".format(
        subsys, subsys
    )

    index = 0
    for d in sorted(diags):
        output += "inline constexpr DiagCode {}(DiagSubsystem::{}, {});\n".format(
            d[1], subsys, index
        )
        index += 1

    output += """
}
"""
    writefile(path, output)


def createsource(path, diags, groups):
    output = """//------------------------------------------------------------------------------
// DiagCode.cpp
// Generated diagnostic helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/diagnostics/AllDiags.h"

#include <ostream>

#include "slang/util/Hash.h"

namespace slang {

static const flat_hash_map<DiagCode, std::tuple<std::string_view, std::string_view, DiagnosticSeverity, std::string_view>> data = {
"""

    for _, v in sorted(diags.items()):
        for d in sorted(v):
            output += '    {{diag::{}, std::make_tuple("{}"sv, "{}"sv, DiagnosticSeverity::{}, "{}"sv)}},\n'.format(
                d[1], d[1], d[2], d[0], d[3]
            )

    output += """};

static const flat_hash_map<std::string_view, std::vector<DiagCode>> optionMap = {
"""

    optionMap = {}
    for _, v in sorted(diags.items()):
        for d in sorted(v):
            name = d[3]
            if not name:
                continue

            if name in optionMap:
                optionMap[name].append(d[1])
            else:
                optionMap[name] = [d[1]]

    for key in sorted(optionMap):
        vals = optionMap[key]
        valstr = ", ".join(["diag::{}".format(v) for v in vals])
        output += '    {{"{}"sv, {{ {} }}}},\n'.format(key, valstr)

    output += """};

static const flat_hash_map<std::string_view, DiagGroup> groupMap = {
"""

    for g in sorted(groups):
        elems = []
        for e in sorted(g[1]):
            elems.extend(optionMap[e])

        elems = ", ".join("diag::{}".format(e) for e in elems)
        output += '    {{"{}"sv, DiagGroup("{}", {{ {} }})}},\n'.format(
            g[0], g[0], elems
        )

    output += """};

std::ostream& operator<<(std::ostream& os, DiagCode code) {
    os << toString(code);
    return os;
}

std::string_view toString(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<0>(it->second);
    return "<user-diag>"sv;
}

std::string_view getDefaultMessage(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<1>(it->second);
    return ""sv;
}

DiagnosticSeverity getDefaultSeverity(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<2>(it->second);
    return DiagnosticSeverity::Ignored;
}

std::string_view getDefaultOptionName(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<3>(it->second);
    return ""sv;
}

std::span<const DiagCode> findDiagsFromOptionName(std::string_view name) {
    if (auto it = optionMap.find(name); it != optionMap.end())
        return it->second;
    return {};
}

const DiagGroup* findDefaultDiagGroup(std::string_view name) {
    if (auto it = groupMap.find(name); it != groupMap.end())
        return &it->second;
    return nullptr;
}

static const DiagCode AllGeneratedCodes[] = {
"""

    for _, v in sorted(diags.items()):
        for d in sorted(v):
            output += "    diag::{},\n".format(d[1])

    output += """};

decltype(DiagCode::KnownCodes) DiagCode::KnownCodes = AllGeneratedCodes;

}"""

    writefile(path, output)


def createallheader(path, diags):
    output = """//------------------------------------------------------------------------------
//! @file AllDiags.h
//! @brief Combined header that includes all subsystem-specific diagnostic headers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

"""

    for k in sorted(diags.keys()):
        output += '#include "slang/diagnostics/{}Diags.h"\n'.format(k)

    output += "\n"
    writefile(path, output)


def createdocs(outDir, inpath, slangBin, diags, groups):
    inf = open(inpath)
    curropt = [None, None, None, None, None]
    inexample = False
    exampleMap = {}

    for line in [x.strip("\n") for x in inf]:
        if not inexample:
            line = line.strip()
            if not line or line.startswith("//"):
                continue

        if inexample:
            if line.startswith("```"):
                inexample = False
            else:
                if curropt[2]:
                    curropt[2] += "\n"
                curropt[2] += line
        elif line.startswith("-W"):
            if curropt:
                exampleMap[curropt[0]] = curropt
            curropt = [line[2:], "", "", "", ""]
        elif line.startswith("```"):
            inexample = True
        elif line.startswith("@options "):
            curropt[4] = line[9:]
        else:
            if curropt[1]:
                curropt[1] += " "
            curropt[1] += line

    if curropt[0]:
        exampleMap[curropt[0]] = curropt

    for k, v in exampleMap.items():
        if not v[2]:
            continue

        testPath = os.path.join(outDir, "test.sv")
        with open(testPath, "w") as outf:
            outf.write(v[2])

        args = [
            slangBin,
            "--quiet",
            "-Wnone",
            "-W" + k,
            "--color-diagnostics",
            testPath,
        ]

        if v[4]:
            args.extend(v[4].split())

        result = subprocess.run(
            args, encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.STDOUT
        )
        v[3] = result.stdout
        if k not in v[3]:
            raise Exception("Test for -W{} is not correct".format(k))

    output = """/** @page warning-ref Warning Reference
@brief Reference information about all supported warnings

@tableofcontents

@section warnings Warnings

"""

    groupMap = {}
    warnlist = []
    for g in groups:
        if g[0] != "default":
            warnlist.append(g)

        for e in g[1]:
            if e in groupMap:
                groupMap[e].add(g[0])
            else:
                groupMap[e] = set([g[0]])

    for _, v in diags.items():
        for d in v:
            if not d[3]:
                continue
            warnlist.append(d)

    warnlist.sort(key=lambda d: d[3] if len(d) > 3 else d[0])

    lastOpt = ""
    for d in warnlist:
        if len(d) > 3:
            opt = d[3]
            if opt == lastOpt:
                continue

            if opt not in exampleMap:
                raise Exception("No documentation for -W{}".format(opt))

            details = exampleMap[opt]
            desc = details[1]
            example = details[2]
            results = details[3]

            if desc == "<ignored>":
                continue

            if lastOpt != "":
                output += "\n@n\n"
            output += "@subsection {} -W{}\n".format(opt, opt)

            output += desc
            output += " @n @n\n"

            if opt in groupMap:
                groups = groupMap[opt]
                if "default" in groups:
                    output += "This diagnostic is enabled by default. @n @n\n"

            if example:
                assert results
                output += "@b Example: \n\n"
                output += "@code{.sv}\n"
                output += example + "\n"
                output += "@endcode\n\n"
                output += "produces:\n\n"
                output += "@code{.ansi}\n"
                output += results
                output += "@endcode\n"

            lastOpt = opt
        else:
            opt = d[0]
            lastOpt = opt
            elemlist = ", ".join("@ref {}".format(s) for s in d[1])

            output += "\n@n\n@subsection {} -W{}\n".format(opt, opt)
            output += "Controls {}.\n@n\n".format(elemlist)

    output += "\n*/"
    writefile(os.path.join(outDir, "warnings.dox"), output)


def checkDiags(path, diags):
    import glob

    for ext in ("cpp", "h"):
        for file in glob.glob(path + "/**/*." + ext, recursive=True):
            with open(file, "r") as f:
                text = f.read()
                diags = [d for d in diags if not ("::" + d) in text]
    return diags


def reportUnused(diags):
    for d in diags:
        print("warning: '{}' is unused".format(d))


if __name__ == "__main__":
    main()
