#!/usr/bin/python

import re
f = open('forth.c', 'r');
out = open('_forthwords.c', 'w');
out.write("// Generated with extract.py\n\n");
for line in f.readlines():
    m = re.search('(i)?(CODE|BINOP|VAR)\(("[^"]+"), ([^,)]+)', line)
    if not m: continue
    out.write("code({}, &&{});\n".format(m.group(3), m.group(4)))
    if m.group(1)=='i':
        out.write("immediate();\n");
f.close()
out.close()
