#!/usr/bin/env python3
"""gen_inputs.py <descriptor> <count> <seed>  -> one line of decimal arguments per input.
Half the values come from a boundary pool (0, +-1, MIN, MAX, MIN+1, MAX-1, powers of two +-1,
small ints, shift distances), the rest uniformly from the full range of the type."""
import random, sys, re
desc, n, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
params = re.findall(r'\[*(?:L[^;]*;|[ZBCSIJFD])', desc[1:desc.index(')')])
rng = random.Random(seed)
def pool(bits):
    lo, hi = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    p = {0, 1, -1, 2, -2, lo, hi, lo + 1, hi - 1, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 65535, 65536}
    for k in range(bits):
        for d in (-1, 0, 1):
            v = (1 << k) + d
            if lo <= v <= hi: p.add(v)
            if lo <= -v <= hi: p.add(-v)
    return sorted(p), lo, hi
P = {'I': pool(32), 'J': pool(64), 'S': pool(16), 'B': pool(8)}
ALPH = list("abcABCxyzXYZ019 .,:;/?&=()[]{}'\"-_+*#%@!~\t\n") + [
    0xe9, 0xc9, 0xdf, 0x130, 0x131, 0x3a3, 0x3c3, 0x3c2, 0xb5, 0xff, 0x178, 0x212a, 0x1e9e,
    0xd801, 0xdc00, 0xdc28, 0x0, 0x660, 0xff11, 0xa0, 0x2000, 0x3000, 0xfeff]
def rstring():
    if rng.random() < 0.05: return "null"
    n = rng.choice([0, 0, 1, 2, 3, 4, 5, 6, 8, 12])
    cs = []
    while len(cs) < n:
        r = rng.random()
        if r < 0.08:  # surrogate pair: Deseret / math letters / emoji
            cp = rng.choice([0x10400, 0x10428, 0x1d400, 0x1f600, 0x10427, 0x1044f])
            cs += [0xd800 + ((cp - 0x10000) >> 10), 0xdc00 + ((cp - 0x10000) & 0x3ff)]
        else:
            c = rng.choice(ALPH)
            cs.append(ord(c) if isinstance(c, str) else c)
    return "s:" + "".join("%04x" % c for c in cs)
def val(t):
    if t == 'Ljava/lang/String;': return rstring()
    if t in P and rng.random() < 0.05: return 0          # divisors / shift distances / zero tests
    if t == 'Z': return rng.randint(0, 1)
    if t == 'C': return rng.choice([0, 1, 65535, rng.randint(0, 65535)])
    p, lo, hi = P[t]
    r = rng.random()
    if r < 0.45: return rng.choice(p)
    if r < 0.6: return rng.randint(-1000, 1000)
    return rng.randint(lo, hi)
out = sys.stdout
for _ in range(n):
    vs = [val(t) for t in params]
    # 3% of the lines: (MIN, -1) in the first two same-typed slots (idiv/irem/ldiv/lrem overflow case)
    if len(params) >= 2 and params[0] == params[1] and params[0] in P and rng.random() < 0.03:
        vs[0], vs[1] = P[params[0]][1], -1
    out.write(" ".join(str(v) for v in vs) + "\n")
