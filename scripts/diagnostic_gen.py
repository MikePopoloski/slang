#!/usr/bin/env python
# This script generates C++ code for compiler diagnostics.
import argparse
import os
import shlex

def main():
    parser = argparse.ArgumentParser(description='Diagnostic source generator')
    parser.add_argument('--dir', default=os.getcwd(), help='Output directory')
    args = parser.parse_args()

    ourdir = os.path.dirname(os.path.realpath(__file__))
    inf = open(os.path.join(ourdir, "diagnostics.txt"))

    headerdir = os.path.join(args.dir, 'slang', 'diagnostics')
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    diags = {}
    subsystem = 'General'

    for line in [x.strip('\n') for x in inf]:
        if not line or line.startswith('//'):
            continue

        parts = shlex.split(line)
        if parts[0] == 'subsystem':
            subsystem = parts[1]
            if subsystem not in diags:
                diags[subsystem] = []
        else:
            sev = parts[0]
            if sev == 'warning':
                diags[subsystem].append(('Warning', parts[2], parts[3], parts[1]))
            elif sev == 'error':
                diags[subsystem].append(('Error', parts[1], parts[2], ''))
            elif sev == 'note':
                diags[subsystem].append(('Note', parts[1], parts[2], ''))
            else:
                raise Exception('Invalid entry: {}'.format(line))

    for k,v in sorted(diags.items()):
        createheader(open(os.path.join(headerdir, k + "Diags.h"), 'w'), k, v)

    createsource(open(os.path.join(args.dir, "DiagCode.cpp"), 'w'), diags)
    createallheader(open(os.path.join(headerdir, "AllDiags.h"), 'w'), diags)

def createheader(outf, subsys, diags):
    outf.write('''//------------------------------------------------------------------------------
// {}Diags.h
// Generated diagnostic enums for the {} subsystem.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"

namespace slang::diag {{

'''.format(subsys, subsys))

    index = 0
    for d in diags:
        outf.write('inline constexpr DiagCode {}(DiagSubsystem::{}, {});\n'.format(d[1], subsys, index))
        index += 1

    outf.write('''
}
''')

def createsource(outf, diags):
    outf.write('''//------------------------------------------------------------------------------
// DiagCode.cpp
// Generated diagnostic helpers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/DiagnosticWriter.h"
#include "slang/diagnostics/AllDiags.h"

#include <flat_hash_map.hpp>

namespace slang {

static const flat_hash_map<DiagCode, std::tuple<string_view, string_view, DiagnosticSeverity>> data = {
''')

    for k,v in sorted(diags.items()):
        for d in v:
            outf.write('    {{diag::{}, std::make_tuple("{}"sv, "{}"sv, DiagnosticSeverity::{})}},\n'.format(
                       d[1], d[1], d[2], d[0]))

    outf.write('''};

std::ostream& operator<<(std::ostream& os, DiagCode code) {
    os << toString(code);
    return os;
}

string_view toString(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<0>(it->second);
    return "<user-diag>"sv;
}

string_view getMessage(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<1>(it->second);
    return ""sv;
}

DiagnosticSeverity getSeverity(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<2>(it->second);
    return DiagnosticSeverity::Error;
}

}
''')

def createallheader(outf, diags):
    outf.write('''//------------------------------------------------------------------------------
// AllDiags.h
// Combined header that includes all subsystem-specific diagnostic headers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

''')

    for k,v in sorted(diags.items()):
        outf.write('#include "slang/diagnostics/{}Diags.h"\n'.format(k))

    outf.write('\n')

if __name__ == "__main__":
    main()
