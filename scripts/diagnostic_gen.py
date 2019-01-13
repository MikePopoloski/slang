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

    diags = []

    for line in [x.strip('\n') for x in inf]:
        if not line or line.startswith('//'):
            continue

        parts = shlex.split(line)
        sev = parts[0]
        if sev == 'warning':
            diags.append(('Warning', parts[2], parts[3], parts[1]))
        elif sev == 'error':
            diags.append(('Error', parts[1], parts[2], ''))
        elif sev == 'note':
            diags.append(('Note', parts[1], parts[2], ''))
        else:
            raise Exception('Invalid entry: {}'.format(line))

    createheader(open(os.path.join(headerdir, "DiagCode.h"), 'w'), diags)
    createsource(open(os.path.join(args.dir, "DiagCode.cpp"), 'w'), diags)

def createheader(outf, diags):
    outf.write('''//------------------------------------------------------------------------------
// DiagCode.h
// Generated diagnostic enums.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

namespace slang {

enum class DiagCode {
''')

    for d in diags:
        outf.write('    {},\n'.format(d[1]))

    outf.write('''};

std::ostream& operator<<(std::ostream& os, DiagCode code);
string_view toString(DiagCode code);

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

namespace slang {

std::ostream& operator<<(std::ostream& os, DiagCode code) {
    os << toString(code);
    return os;
}

string_view toString(DiagCode code) {
    switch (code) {
''')

    for d in diags:
        outf.write('        case DiagCode::{}: return "{}";\n'.format(d[1], d[1]))

    outf.write('''        default: return "";
    }
}

string_view getMessage(DiagCode code) {
    switch (code) {
''')

    for d in diags:
        outf.write('        case DiagCode::{}: return "{}";\n'.format(d[1], d[2]))

    outf.write('''        default: return "";
    }
}

DiagnosticSeverity getSeverity(DiagCode code) {
    switch (code) {
''')

    for d in diags:
        outf.write('        case DiagCode::{}: return DiagnosticSeverity::{};\n'.format(d[1], d[0]))

    outf.write('''        default: return DiagnosticSeverity::Error;
    }
}

}
''')

if __name__ == "__main__":
    main()
