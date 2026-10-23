#!/usr/bin/env python3
"""compare.py <inputs> <hotspot.out> <model.out> -> summary; exit 1 on any mismatch."""
import sys
inp = open(sys.argv[1]).read().splitlines()
hs = open(sys.argv[2]).read().splitlines()
md = open(sys.argv[3]).read().splitlines()
if not (len(inp) == len(hs) == len(md)):
    print("LENGTH MISMATCH inputs=%d hotspot=%d model=%d" % (len(inp), len(hs), len(md))); sys.exit(1)
bad = [(i, h, m) for i, h, m in zip(inp, hs, md) if h != m]
exc = sum(1 for h in hs if h.startswith('E '))
print("inputs=%d agree=%d mismatches=%d hotspot_exceptions=%d" % (len(inp), len(inp) - len(bad), len(bad), exc))
for i, h, m in bad[:10]:
    print("  args=[%s] hotspot=%s model=%s" % (i, h, m))
sys.exit(1 if bad else 0)
