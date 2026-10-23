#!/usr/bin/env python3
"""Compare model and JVM outputs of the float/double differential test.

usage: compare.py WORKDIR [--canary]

Normal mode: for every OP with WORKDIR/OP.in, compare WORKDIR/OP.model
against WORKDIR/OP.java line by line.
--canary: compare deliberately mismatched pairs (model OP1 vs JVM OP2, and
mutant models vs the JVM); here mismatches are EXPECTED.
Exit status 1 if (normal mode) any mismatch or missing/short file."""
import os, sys

OPS = ["fadd", "fsub", "fmul", "fdiv", "frem", "fneg", "fneg_raw",
       "dadd", "dsub", "dmul", "ddiv", "drem", "dneg", "dneg_raw",
       "i2f", "i2d", "l2f", "l2d", "f2d", "d2f", "f2i", "f2l", "d2i", "d2l",
       "fcmpl", "fcmpg", "dcmpl", "dcmpg"]

CANARIES = [  # (label, model output file, jvm output file, input file)
    ("model fadd vs JVM fsub", "fadd.model", "fsub.java", "fadd.in"),
    ("model dadd vs JVM dsub", "dadd.model", "dsub.java", "dadd.in"),
    ("model fcmpl vs JVM fcmpg", "fcmpl.model", "fcmpg.java", "fcmpl.in"),
    ("mutant ties-away fadd vs JVM fadd", "mut_tiesaway_fadd.model", "fadd.java", "fadd.in"),
    ("mutant ties-away dadd vs JVM dadd", "mut_tiesaway_dadd.model", "dadd.java", "dadd.in"),
    ("mutant ties-away fmul vs JVM fmul", "mut_tiesaway_fmul.model", "fmul.java", "fmul.in"),
    ("mutant ties-away dmul vs JVM dmul", "mut_tiesaway_dmul.model", "dmul.java", "dmul.in"),
    ("mutant flush-to-zero fadd vs JVM fadd", "mut_ftz_fadd.model", "fadd.java", "fadd.in"),
    ("mutant flush-to-zero dadd vs JVM dadd", "mut_ftz_dadd.model", "dadd.java", "dadd.in"),
    ("mutant flush-to-zero fmul vs JVM fmul", "mut_ftz_fmul.model", "fmul.java", "fmul.in"),
    ("mutant flush-to-zero dmul vs JVM dmul", "mut_ftz_dmul.model", "dmul.java", "dmul.in"),
]

def lines(p):
    with open(p) as f:
        return f.read().split("\n")[:-1]

def cmp(work, label, mfile, jfile, infile, show=3):
    ins = lines(os.path.join(work, infile))
    m = lines(os.path.join(work, mfile))
    j = lines(os.path.join(work, jfile))
    ok = len(ins) == len(m) == len(j)
    bad = [i for i in range(min(len(m), len(j))) if m[i] != j[i]]
    print(f"{label:40s} inputs={len(ins):8d} mismatches={len(bad):8d}" + ("" if ok else "  LENGTH MISMATCH"))
    for i in bad[:show]:
        print(f"    in: {ins[i]:35s} model: {m[i]:18s} jvm: {j[i]}")
    return len(bad), ok

def main():
    work = sys.argv[1]
    canary = "--canary" in sys.argv
    if canary:
        for label, mf, jf, inf in CANARIES:
            if os.path.exists(os.path.join(work, mf)):
                cmp(work, label, mf, jf, inf, show=2)
        return 0
    total = 0; allok = True
    for op in OPS:
        if not os.path.exists(os.path.join(work, op + ".in")):
            continue
        n, ok = cmp(work, op, op + ".model", op + ".java", op + ".in", show=10)
        total += n; allok &= ok
    print(f"TOTAL mismatches: {total}")
    return 0 if (total == 0 and allok) else 1

sys.exit(main())
