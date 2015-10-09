# Takes an input text file containing the SystemVerilog language grammar
# and converts it to nice linked markdown.

import re
import os

ourdir = os.path.dirname(os.path.realpath(__file__))

inf = open(os.path.join(ourdir, 'grammar.txt'))
outf = open(os.path.join(ourdir, '../docs/grammar.md'), 'w')

outf.write('# SystemVerilog\n')

for line in inf:
	line = line.strip()
	if len(line) == 0:
		continue

	if line.startswith('A.'):
		count = line.split(' ')[0].count('.')
		if count == 1:
			outf.write('## ')
		elif count == 2:
			outf.write('### ')
		elif count == 3:
			outf.write('#### ')
		else:
			raise Exception("wut")
		outf.write(line + '\n')
	else:
		match = re.match(r'(\w+) ::=', line)
		if match:
			s = match.group(1)
			outf.write('<a name="{}"></a>{} ::='.format(s, s.replace('_', '\\_')))
			line = line[len(match.group(0)):]
		else:
			outf.write('&nbsp;&nbsp;&nbsp;&nbsp;')

		def replacer(m):
			s = m.group(1)
			t = s
			for c in ['*', '-', '|', '[', '{', '_']:
				t = t.replace(c, '\\' + c)
			if s not in ['|', '[', ']', '{', '}']:
				return '`{}`'.format(s)
			else:
				return t

		line = line.replace('{,', '{ ,')
		line = re.sub(r'([^\w\s]+)', replacer, line)
		line = re.sub(r'(\w+)', r'[\1](#\1)', line)
		outf.write(line + '  \n')
