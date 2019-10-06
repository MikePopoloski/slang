#!/usr/bin/env python
# This script generates C++ code for compiler diagnostics.
import argparse
import os
import shlex

def writefile(path, contents):
    try:
        with open(path, 'r') as f:
            existing = f.read()
    except:
        existing = ''

    if existing != contents:
        with open(path, 'w') as f:
            f.write(contents)

def main():
    parser = argparse.ArgumentParser(description='Diagnostic source generator')
    parser.add_argument('--outDir', default=os.getcwd(), help='Output directory')
    parser.add_argument('--srcDir', help='Source directory to search for usages')
    parser.add_argument('--incDir', help='Include directory to search for usages')
    args = parser.parse_args()

    ourdir = os.path.dirname(os.path.realpath(__file__))
    inf = open(os.path.join(ourdir, "diagnostics.txt"))

    headerdir = os.path.join(args.outDir, 'slang', 'diagnostics')
    try:
        os.makedirs(headerdir)
    except OSError:
        pass

    diags = {}
    groups = []
    diaglist = []
    subsystem = 'General'
    curgroup = None

    def parsegroup(elems):
        nonlocal curgroup
        for e in elems:
            if e == '}':
                groups.append(curgroup)
                curgroup = None
                break
            curgroup[1].append(e)

    for line in [x.strip('\n') for x in inf]:
        if not line or line.startswith('//'):
            continue

        parts = shlex.split(line)
        if curgroup:
            parsegroup(parts)
        elif parts[0] == 'subsystem':
            subsystem = parts[1]
            if subsystem not in diags:
                diags[subsystem] = []
        elif parts[0] == 'group':
            curgroup = (parts[1], [])
            assert(parts[2] == '=')
            assert(parts[3] == '{')
            parsegroup(parts[4:])
        else:
            sev = parts[0]
            if sev == 'warning':
                diags[subsystem].append(('Warning', parts[2], parts[3], parts[1]))
                diaglist.append(parts[2])
            elif sev == 'error':
                diags[subsystem].append(('Error', parts[1], parts[2], ''))
                diaglist.append(parts[1])
            elif sev == 'note':
                diags[subsystem].append(('Note', parts[1], parts[2], ''))
                diaglist.append(parts[1])
            else:
                raise Exception('Invalid entry: {}'.format(line))

    for k,v in sorted(diags.items()):
        createheader(os.path.join(headerdir, k + "Diags.h"), k, v)

    createsource(os.path.join(args.outDir, "DiagCode.cpp"), diags, groups)
    createallheader(os.path.join(headerdir, "AllDiags.h"), diags)

    doCheck = False
    if doCheck:
        diaglist = checkDiags(args.srcDir, diaglist)
        diaglist = checkDiags(args.incDir, diaglist)
        reportUnused(diaglist)

def createheader(path, subsys, diags):
    output = '''//------------------------------------------------------------------------------
// {}Diags.h
// Generated diagnostic enums for the {} subsystem.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"

namespace slang::diag {{

'''.format(subsys, subsys)

    index = 0
    for d in diags:
        output += 'inline constexpr DiagCode {}(DiagSubsystem::{}, {});\n'.format(d[1], subsys, index)
        index += 1

    output += '''
}
'''
    writefile(path, output)

def createsource(path, diags, groups):
    output = '''//------------------------------------------------------------------------------
// DiagCode.cpp
// Generated diagnostic helpers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/diagnostics/AllDiags.h"

#include <flat_hash_map.hpp>

namespace slang {

static const flat_hash_map<DiagCode, std::tuple<string_view, string_view, DiagnosticSeverity, string_view>> data = {
'''

    for k,v in sorted(diags.items()):
        for d in v:
            output += '    {{diag::{}, std::make_tuple("{}"sv, "{}"sv, DiagnosticSeverity::{}, "{}"sv)}},\n'.format(
                       d[1], d[1], d[2], d[0], d[3] if len(d) > 2 else '')

    output += '''};

static const flat_hash_map<string_view, DiagCode> optionMap = {
'''

    optionMap = {}
    for k,v in sorted(diags.items()):
        for d in v:
            if not d[3]:
                continue
            output += '    {{"{}"sv, diag::{}}},\n'.format(d[3], d[1])
            optionMap[d[3]] = d[1]
    output += '''};

static const flat_hash_map<string_view, DiagGroup> groupMap = {
'''

    for g in sorted(groups):
        elems = ', '.join('diag::{}'.format(optionMap[e]) for e in g[1])
        output += '    {{"{}"sv, DiagGroup("{}", {{ {} }})}},\n'.format(g[0], g[0], elems)

    output += '''};

std::ostream& operator<<(std::ostream& os, DiagCode code) {
    os << toString(code);
    return os;
}

string_view toString(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<0>(it->second);
    return "<user-diag>"sv;
}

string_view getDefaultMessage(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<1>(it->second);
    return ""sv;
}

DiagnosticSeverity getDefaultSeverity(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<2>(it->second);
    return DiagnosticSeverity::Ignored;
}

string_view getDefaultOptionName(DiagCode code) {
    if (auto it = data.find(code); it != data.end())
        return std::get<3>(it->second);
    return ""sv;
}

DiagCode findDiagFromOptionName(string_view name) {
    if (auto it = optionMap.find(name); it != optionMap.end())
        return it->second;
    return DiagCode();
}

const DiagGroup* findDefaultDiagGroup(string_view name) {
    if (auto it = groupMap.find(name); it != groupMap.end())
        return &it->second;
    return nullptr;
}

}
'''
    writefile(path, output)

def createallheader(path, diags):
    output = '''//------------------------------------------------------------------------------
// AllDiags.h
// Combined header that includes all subsystem-specific diagnostic headers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

'''

    for k,v in sorted(diags.items()):
        output += '#include "slang/diagnostics/{}Diags.h"\n'.format(k)

    output += '\n'
    writefile(path, output)

def checkDiags(path, diags):
    import glob
    for ext in ('cpp', 'h'):
        for file in glob.glob(path + "/**/*." + ext, recursive=True):
            with open(file, 'r') as f:
                text = f.read()
                diags = [d for d in diags if not ('::' + d) in text]
    return diags

def reportUnused(diags):
    for d in diags:
        print("warning: '{}' is unused".format(d))

if __name__ == "__main__":
    main()