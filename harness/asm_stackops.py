#!/usr/bin/env python3
"""Assemble StackOps.class (class file version 61) exercising every JVMS form of the
stack instructions javac rarely emits: pop, pop2 (2 forms), dup, dup_x1, dup_x2 (2),
dup2 (2), dup2_x1 (2), dup2_x2 (4), swap.

Each method loads its parameters, executes one stack instruction, pops the whole
resulting stack into fresh locals and returns an order-sensitive long hash of them,
so HotSpot and the model must agree on the exact resulting stack.
Straight-line code only, so no StackMapTable is needed; HotSpot's verifier checks it.

    harness/asm_stackops.py <outdir>      -> <outdir>/StackOps.class
"""
import struct, sys, os

OPS = {'nop': 0, 'pop': 87, 'pop2': 88, 'dup': 89, 'dup_x1': 90, 'dup_x2': 91, 'dup2': 92,
       'dup2_x1': 93, 'dup2_x2': 94, 'swap': 95}

# name, parameter types (I=int, J=long, bottom first), op
CASES = [
    ('pop',      'II',   'pop'),
    ('pop2_f1',  'III',  'pop2'),
    ('pop2_f2',  'IJ',   'pop2'),
    ('dup',      'I',    'dup'),
    ('dup_x1',   'II',   'dup_x1'),
    ('dup_x2_f1', 'III', 'dup_x2'),
    ('dup_x2_f2', 'JI',  'dup_x2'),
    ('dup2_f1',  'II',   'dup2'),
    ('dup2_f2',  'J',    'dup2'),
    ('dup2_x1_f1', 'III', 'dup2_x1'),
    ('dup2_x1_f2', 'IJ', 'dup2_x1'),
    ('dup2_x2_f1', 'IIII', 'dup2_x2'),
    ('dup2_x2_f2', 'IIJ', 'dup2_x2'),
    ('dup2_x2_f3', 'JII', 'dup2_x2'),
    ('dup2_x2_f4', 'JJ',  'dup2_x2'),
    ('swap',     'II',   'swap'),
    ('nop',      'IJ',   'nop'),
]

def simulate(op, st):
    """st: list of types, bottom first. Returns the new list per JVMS 6.5."""
    c2 = lambda t: t == 'J'
    s = list(st)
    v1 = s[-1] if s else None
    if op == 'nop': return s
    if op == 'pop': return s[:-1]
    if op == 'pop2': return s[:-1] if c2(v1) else s[:-2]
    if op == 'dup': return s + [v1]
    if op == 'dup_x1': return s[:-2] + [s[-1], s[-2], s[-1]]
    if op == 'dup_x2':
        if c2(s[-2]): return s[:-2] + [s[-1], s[-2], s[-1]]
        return s[:-3] + [s[-1], s[-3], s[-2], s[-1]]
    if op == 'dup2':
        if c2(v1): return s + [v1]
        return s + s[-2:]
    if op == 'dup2_x1':
        if c2(v1): return s[:-2] + [s[-1], s[-2], s[-1]]
        return s[:-3] + [s[-2], s[-1], s[-3], s[-2], s[-1]]
    if op == 'dup2_x2':
        if c2(v1) and c2(s[-2]): return s[:-2] + [s[-1], s[-2], s[-1]]
        if c2(v1): return s[:-3] + [s[-1], s[-3], s[-2], s[-1]]
        if c2(s[-3]): return s[:-3] + [s[-2], s[-1], s[-3], s[-2], s[-1]]
        return s[:-4] + [s[-2], s[-1], s[-4], s[-3], s[-2], s[-1]]
    if op == 'swap': return s[:-2] + [s[-1], s[-2]]
    raise ValueError(op)

class CP:
    def __init__(self): self.e = []; self.idx = {}
    def add(self, key, data):
        if key not in self.idx:
            self.e.append(data); self.idx[key] = len(self.e)
        return self.idx[key]
    def utf8(self, s): b = s.encode(); return self.add(('u', s), struct.pack('>BH', 1, len(b)) + b)
    def cls(self, s): n = self.utf8(s); return self.add(('c', s), struct.pack('>BH', 7, n))
    def bytes(self): return struct.pack('>H', len(self.e) + 1) + b''.join(self.e)

def method_code(params, op):
    code = bytearray(); slot = 0
    # load parameters (bottom of the stack first)
    for t in params:
        if t == 'I': code += bytes([21, slot]); slot += 1      # iload
        else: code += bytes([22, slot]); slot += 2             # lload
    code.append(OPS[op])
    st = simulate(op, list(params))
    # pop everything into locals, top first
    stored = []; base = 20
    for t in reversed(st):
        if t == 'I': code += bytes([54, base]); stored.append((t, base)); base += 1   # istore
        else: code += bytes([55, base]); stored.append((t, base)); base += 2         # lstore
    code.append(9)  # lconst_0 accumulator
    for k, (t, s) in enumerate(stored):
        if t == 'I': code += bytes([21, s, 133])     # iload; i2l
        else: code += bytes([22, s])                 # lload
        code += bytes([17]) + struct.pack('>h', 1000 + 37 * k) + bytes([133, 105, 131])  # sipush K; i2l; lmul; lxor
        code += bytes([16, 31, 133, 105])             # bipush 31; i2l; lmul (order-sensitive)
    code.append(173)  # lreturn
    return bytes(code), base

def main():
    out = sys.argv[1]
    cp = CP()
    this = cp.cls('StackOps'); sup = cp.cls('java/lang/Object'); codeu = cp.utf8('Code')
    meths = []
    for name, params, op in CASES:
        desc = '(' + params + ')J'
        code, maxl = method_code(params, op)
        attr = struct.pack('>HHI', 16, maxl, len(code)) + code + struct.pack('>HH', 0, 0)
        m = struct.pack('>HHHH', 0x0009, cp.utf8(name), cp.utf8(desc), 1)  # public static
        m += struct.pack('>HI', codeu, len(attr)) + attr
        meths.append(m)
    body = struct.pack('>HHH', 0x0021, this, sup) + struct.pack('>H', 0) + struct.pack('>H', 0)
    body += struct.pack('>H', len(meths)) + b''.join(meths) + struct.pack('>H', 0)
    data = struct.pack('>IHH', 0xCAFEBABE, 0, 61) + cp.bytes() + body
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, 'StackOps.class'), 'wb').write(data)
    for name, params, op in CASES:
        print(out, 'StackOps', name, '(' + params + ')J')

if __name__ == '__main__':
    main()
