#!/usr/bin/env python3
"""Check the Unicode facts assumed by theories/Camel/CimSpec.v (jdk_facts) and by
cih_inconsistent_supplementary against the JDK's own tables (harness/work/unicode-21.txt,
written by harness/java/UnicodeTables.java)."""
import sys
up, lo = {}, {}
for line in open(sys.argv[1] if len(sys.argv) > 1 else 'harness/work/unicode-21.txt'):
    if line.startswith('#'): continue
    cp, u, l, d, f = map(int, line.split()); up[cp] = u; lo[cp] = l
U = lambda c: up.get(c, c); L = lambda c: lo.get(c, c)
ok = True
def check(name, bad):
    global ok
    print("%-40s %s" % (name, "ok" if not bad else "VIOLATED %s" % bad[:5])); ok &= not bad
check("uenv_ascii", [c for c in range(128) if not (U(c) == (c - 32 if 97 <= c <= 122 else c) and L(c) == (c + 32 if 65 <= c <= 90 else c))])
check("latin1_facts", [x for x in range(192, 223) if x != 215 and not (U(x) == x and U(x + 32) == x)])
check("bmp_closed", [c for c in range(65536) if not (U(c) < 65536 and L(c) < 65536)])
check("deseret pair U+10428 -> U+10400", [] if U(0x10428) == 0x10400 and U(0x10400) == 0x10400 else ['no'])
check("surrogate units map to themselves", [c for c in range(0xd800, 0xe000) if U(c) != c or L(c) != c])
sys.exit(0 if ok else 1)
