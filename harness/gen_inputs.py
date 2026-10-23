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
def val(t):
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
