#!/usr/bin/env python
# This script generates C++ source for parse tree syntax nodes from a data file.

import os

def main():
	ourdir = os.path.dirname(os.path.realpath(__file__))
	inf = open(os.path.join(ourdir, "syntax.txt"))
	outf = open(os.path.join(ourdir, "../source/parsing/AllSyntax.h"), 'w')

	outf.write('''//------------------------------------------------------------------------------
// AllSyntax.h
// All generated syntax node data structures.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "lexing/Token.h"
#include "util/BumpAllocator.h"
#include "SyntaxNode.h"

// This file contains all parse tree syntax nodes.
// It is auto-generated by the syntax_gen.py script under the tools/ directory.

namespace slang {

''')

	currtype = None
	currkind = None
	currtype_name = None
	tags = None
	alltypes = {}
	kindmap = {}

	alltypes['SyntaxNode'] = (None, None, None, '')

	for line in [x.strip('\n') for x in inf]:
		if line.startswith('//'):
			outf.write(line)
			outf.write('\n\n')
		elif len(line) == 0 or (currtype is not None and line == 'empty'):
			if currtype is not None:
				generate(outf, currtype_name, tags, currtype, alltypes, kindmap)
			currtype = None
			currkind = None
		elif currtype is not None:
			p = line.split(' ')
			if len(p) != 2:
				raise Exception("Two elements per member please.")
			currtype.append(p)
		elif currkind is not None:
			for k in line.split(' '):
				if k in kindmap:
					raise Exception("More than one kind map for {}".format(k))
				kindmap[k] = currkind
		elif line.startswith('forward '):
			outf.write('struct {};\n'.format(line[8:]))
		elif line.startswith('kindmap<'):
			currkind = line[8:line.index('>')]
		else:
			p = line.split(' ')
			currtype_name = p[0]
			tags = p[1:] if len(p) > 1 else None
			currtype = []

	if currtype:
		generate(outf, currtype_name, tags, currtype, alltypes, kindmap)

	# Write out a dispatch method to get from SyntaxKind to actual concrete type
	outf.write('template<typename T>\n')
	outf.write('void dispatchVisitor(T& v, const SyntaxNode* node) {\n')
	outf.write('    if (!node) return;\n')
	outf.write('    switch (node->kind) {\n')
	outf.write('        case SyntaxKind::Unknown: break;\n')
	outf.write('        case SyntaxKind::List: v.visitDefault(*node); break;\n')

	for k,v in kindmap.items():
		outf.write('        case SyntaxKind::{}: '.format(k))
		outf.write('SyntaxNode::dispatch(v, *(const {0}*)node); break;\n'.format(v))
		alltypes.pop(v, None)

	outf.write('    }\n')
	outf.write('}\n\n')

	outf.write('}')

	# Do some checking to make sure all types have at least one kind assigned,
	# or has set final=false. We already removed types from alltypes in the
	# loop above.
	for k,v in alltypes.items():
		if v[3]: # Check for final
			print("Type '{}' has no kinds assigned to it.".format(k))

def generate(outf, name, tags, members, alltypes, kindmap):
	tagdict = {}
	if tags:
		for t in tags:
			p = t.split('=')
			tagdict[p[0]] = p[1]

	base = tagdict['base'] if 'base' in tagdict else 'SyntaxNode'
	outf.write('struct {} : public {} {{\n'.format(name, base))

	pointerMembers = set()
	processed_members = []
	baseInitializers = ''
	combined = members
	if base != 'SyntaxNode':
		processed_members.extend(alltypes[base][0])
		pointerMembers = pointerMembers.union(alltypes[base][2])
		baseInitializers = ', '.join([x[1] for x in alltypes[base][1]])
		if baseInitializers:
			baseInitializers = ', ' + baseInitializers
		combined = alltypes[base][1] + members

	for m in members:
		if m[0] == 'token':
			typename = 'Token'
		elif m[0] == 'tokenlist':
			typename = 'TokenList'
			pointerMembers.add(m[1])
		elif m[0].startswith('list<'):
			typename = 'SyntaxList<' + m[0][5:]
			pointerMembers.add(m[1])
		elif m[0].startswith('separated_list<'):
			typename = 'SeparatedSyntaxList<' + m[0][15:]
			pointerMembers.add(m[1])
		else:
			optional = False
			if m[0].endswith('?'):
				optional = True
				m[0] = m[0][:-1]

			if m[0] not in alltypes:
				raise Exception("Unknown type '{}'".format(m[0]))

			if optional:
				typename = m[0] + '*'
			else:
				pointerMembers.add(m[1])
				typename = m[0] + '&'

		l = '{} {}'.format(typename, m[1])
		processed_members.append(l)
		outf.write('    {};\n'.format(l))

	kindArg = 'SyntaxKind kind' if 'kind' not in tagdict else ''
	kindValue = 'kind' if 'kind' not in tagdict else 'SyntaxKind::' + tagdict['kind']

	if 'kind' in tagdict:
		k = tagdict['kind']
		if k in kindmap:
			raise Exception("More than one kind map for {}".format(k))
		kindmap[k] = name

	if kindArg and len(processed_members) > 0:
		kindArg += ', '

	initializers = ', '.join(['{0}({0})'.format(x[1]) for x in members])
	if initializers:
		initializers = ', ' + initializers

	final = ' final'
	if 'final' in tagdict and tagdict['final'] == 'false':
		final = ''

	alltypes[name] = (processed_members, members, pointerMembers, final)

	outf.write('\n')
	outf.write('    {}({}{}) :\n'.format(name, kindArg, ', '.join(processed_members)))
	outf.write('        {}({}{}){}\n'.format(base, kindValue, baseInitializers, initializers))
	outf.write('    {\n')

	if len(members) == 0 and final == '':
		outf.write('    }\n')
	else:
		outf.write('        childCount += {};\n'.format(len(members)))
		outf.write('    }\n\n')

		outf.write('    {}(const {}&) = delete;\n'.format(name, name))
		outf.write('    {}& operator=(const {}&) = delete;\n\n'.format(name, name))

		outf.write('protected:\n')
		outf.write('    TokenOrSyntax getChild(uint32_t index) override{} {{\n'.format(final))

		if len(combined) > 0:
			outf.write('        switch (index) {\n')

			index = 0
			for m in combined:
				addr = '&' if m[1] in pointerMembers else ''
				outf.write('            case {}: return {}{};\n'.format(index, addr, m[1]))
				index += 1

			outf.write('            default: return nullptr;\n')
			outf.write('        }\n')
		else:
			outf.write('        (void)index;\n')
			outf.write('        return nullptr;\n')

		outf.write('    }\n\n')

		outf.write('    void replaceChild(uint32_t index, Token token) override{} {{\n'.format(final))
		anyTokens = False
		if len(combined) > 0:
			outf.write('        switch (index) {\n')
			index = 0
			for m in combined:
				isToken = m[0] == "token"
				if isToken:
					anyTokens = True
				statement = "ASSERT(false)" if not isToken else "{} = token".format(m[1])
				outf.write('            case {}: {}; break;\n'.format(index, statement))
				index += 1

			outf.write('        }\n')
		else:
			outf.write('        (void)index;\n')

		if not anyTokens:
			outf.write('        (void)token;\n')
		outf.write('    }\n')

	outf.write('};\n\n')

if __name__ == "__main__":
	main()
