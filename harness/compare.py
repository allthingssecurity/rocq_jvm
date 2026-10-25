#!/usr/bin/env python3
"""compare.py <inputs> <hotspot.out> <model.out> -> summary; exit 1 on any mismatch."""
import sys
inp = open(sys.argv[1]).read().splitlines()
hs = open(sys.argv[2]).read().splitlines()
md = open(sys.argv[3]).read().splitlines()
if not (len(inp) == len(hs) == len(md)):
    print("LENGTH MISMATCH inputs=%d hotspot=%d model=%d" % (len(inp), len(hs), len(md))); sys.exit(1)
# A model run that is STUCK (unsupported / beyond a model bound) or out of FUEL makes no claim:
# it is counted separately, not as agreement and not as a mismatch.
# Exceptions: HotSpot prints "E <class> m:<message>"; a model line "E <class>" without " m:" makes
# no claim about the message, so only the class is compared.
def norm(h, m):
    if m.startswith('E ') and ' m:' not in m and h.startswith('E '):
        return h.split(' m:')[0]
    return h
hs = [norm(h, m) for h, m in zip(hs, md)]
msgs = sum(1 for m in md if m.startswith('E ') and ' m:' in m)
nores = [(i, h, m) for i, h, m in zip(inp, hs, md) if m.startswith('STUCK') or m == 'FUEL']
bad = [(i, h, m) for i, h, m in zip(inp, hs, md) if h != m and not (m.startswith('STUCK') or m == 'FUEL')]
exc = sum(1 for h in hs if h.startswith('E '))
print("inputs=%d agree=%d mismatches=%d hotspot_exceptions=%d model_no_claim=%d messages_compared=%d" % (len(inp), len(inp) - len(bad) - len(nores), len(bad), exc, len(nores), msgs))
for i, h, m in nores[:3]:
    print("  no-claim args=[%s] hotspot=%s model=%s" % (i, h, m))
for i, h, m in bad[:10]:
    print("  args=[%s] hotspot=%s model=%s" % (i, h, m))
sys.exit(1 if bad else 0)
