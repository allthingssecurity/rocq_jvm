#!/usr/bin/env python3
"""Opcode coverage report vs JVMS SE 21 chapter 6 -> docs/opcode-coverage.md

Columns: decoded (ClassFile.v decodes it; true for all 202 opcodes), semantics (Semantics.v
executes it; list below kept in sync by hand with Semantics.step), and differentially tested
(the opcode occurs in a class file of the differential targets: we scan the bytecode with javap)."""
import subprocess, re, sys, os
os.chdir(os.path.join(os.path.dirname(__file__), '..'))
NAMES = """nop aconst_null iconst_m1 iconst_0 iconst_1 iconst_2 iconst_3 iconst_4 iconst_5 lconst_0 lconst_1
fconst_0 fconst_1 fconst_2 dconst_0 dconst_1 bipush sipush ldc ldc_w ldc2_w iload lload fload dload aload
iload_0 iload_1 iload_2 iload_3 lload_0 lload_1 lload_2 lload_3 fload_0 fload_1 fload_2 fload_3 dload_0
dload_1 dload_2 dload_3 aload_0 aload_1 aload_2 aload_3 iaload laload faload daload aaload baload caload
saload istore lstore fstore dstore astore istore_0 istore_1 istore_2 istore_3 lstore_0 lstore_1 lstore_2
lstore_3 fstore_0 fstore_1 fstore_2 fstore_3 dstore_0 dstore_1 dstore_2 dstore_3 astore_0 astore_1
astore_2 astore_3 iastore lastore fastore dastore aastore bastore castore sastore pop pop2 dup dup_x1
dup_x2 dup2 dup2_x1 dup2_x2 swap iadd ladd fadd dadd isub lsub fsub dsub imul lmul fmul dmul idiv ldiv
fdiv ddiv irem lrem frem drem ineg lneg fneg dneg ishl lshl ishr lshr iushr lushr iand land ior lor ixor
lxor iinc i2l i2f i2d l2i l2f l2d f2i f2l f2d d2i d2l d2f i2b i2c i2s lcmp fcmpl fcmpg dcmpl dcmpg ifeq
ifne iflt ifge ifgt ifle if_icmpeq if_icmpne if_icmplt if_icmpge if_icmpgt if_icmple if_acmpeq if_acmpne
goto jsr ret tableswitch lookupswitch ireturn lreturn freturn dreturn areturn return getstatic putstatic
getfield putfield invokevirtual invokespecial invokestatic invokeinterface invokedynamic new newarray
anewarray arraylength athrow checkcast instanceof monitorenter monitorexit wide multianewarray ifnull
ifnonnull goto_w jsr_w""".split()
assert len(NAMES) == 202, len(NAMES)
SEM = set(NAMES) - {'jsr', 'ret', 'jsr_w'}
PARTIAL = {'ldc': 'int/float/String/Class constants; MethodType/MethodHandle/dynamic constants not yet',
           'ldc_w': 'as ldc', 'ldc2_w': 'long/double constants (dynamic constants not yet)',
           'invokedynamic': 'javac string concatenation (StringConcatFactory) and lambdas/method refs (LambdaMetafactory.metafactory, except Foo::new); altMetafactory, records, switch patterns not yet',
           'invokevirtual': 'loaded classes + JDK methods that have a model (TRUST.md)',
           'invokeinterface': 'as invokevirtual; maximally-specific default methods, private interface methods (JVMS 5.4.6); lambda objects',
           'invokestatic': 'as invokevirtual', 'invokespecial': 'as invokevirtual',
           'monitorenter': 'single thread: entry counts only (threads: Track C)', 'monitorexit': 'as monitorenter',
           'getstatic': 'field resolution through superclasses and superinterfaces (JVMS 5.4.3.2), initialises the declaring class; JDK static fields with a model (Boolean.TRUE/FALSE)'}
SEM |= set(PARTIAL)
targets = set()
for t in ('harness/targets-phase1.txt', 'harness/targets-stackops.txt', 'harness/targets-ops2.txt', 'harness/targets-heap.txt', 'harness/targets-strs.txt', 'harness/targets-flt.txt', 'harness/targets-lam.txt',
          'harness/targets-fld.txt', 'harness/targets-sel.txt'):
    for line in open(t):
        if line.strip():
            d, c, m, desc = line.split()[:4]
            targets.add((d, c, m, desc))
seen = {}
for d, c in sorted({(t[0], t[1]) for t in targets}):
    out = subprocess.run(['javap', '-c', '-p', '-s', '-cp', d, c], capture_output=True, text=True).stdout
    # split into methods: header line, then "descriptor: ...", then Code
    for blk in re.split(r'\n(?=  \S)', out):
        hm = re.match(r'\s*(?:[\w.<>\[\]$,]+\s+)*?([\w$<>]+)\(', blk)
        dm = re.search(r'descriptor: (\S+)', blk)
        if not hm or not dm or (d, c, hm.group(1), dm.group(1)) not in targets:
            continue
        for m in re.finditer(r'^\s+\d+: ([a-z_0-9]+)(.*)$', blk, re.M):
            op, rest = m.group(1), m.group(2)
            if op.endswith('_w') and op not in ('ldc_w', 'ldc2_w', 'goto_w', 'jsr_w'):
                op = op[:-2]; seen['wide'] = seen.get('wide', 0) + 1   # javap: iload_w = wide iload
            seen[op] = seen.get(op, 0) + 1
            # javap shows wide forms as the base opcode with an index > 255
            if op in ('iload', 'lload', 'aload', 'istore', 'lstore', 'astore', 'iinc'):
                nums = re.findall(r'-?\d+', rest)
                if nums and int(nums[0]) > 255 or (op == 'iinc' and len(nums) > 1 and not -128 <= int(nums[1]) <= 127):
                    seen['wide'] = seen.get('wide', 0) + 1
rows = []
for i, n in enumerate(NAMES):
    sem = 'yes' if n in SEM else 'no'
    if n in PARTIAL: sem = 'partial: ' + PARTIAL[n]
    rows.append('| %d | %s | yes | %s | %s |' % (i if i < 202 else i, n, sem, 'yes (%d sites)' % seen[n] if n in seen else 'no'))
nsem = sum(1 for n in NAMES if n in SEM)
ntest = sum(1 for n in NAMES if n in SEM and n in seen)
hdr = ["# Opcode coverage (generated by tools/coverage.py)", "",
       "JVMS SE 21 chapter 6 has 202 opcodes (0-201). All are decoded by `theories/Loader/ClassFile.v`.",
       "", "- with semantics in `theories/Core/Semantics.v`: **%d** (%d of them partially)" % (nsem, len(PARTIAL)),
       "- of those, occurring in the differentially tested bytecode: **%d**" % ntest,
       "- `jsr`, `ret`, `jsr_w` are decoded but rejected: class files of version >= 51 cannot contain them.",
       "- Semantics: frame-local opcodes in `theories/Core/Semantics.v` (+ `Float.v`), heap/call/class opcodes in `theories/Core/Machine.v`, JDK methods in `theories/Jdk/`.",
       "", "| code | opcode | decoded | semantics | differentially tested |", "|---|---|---|---|---|"]
open('docs/opcode-coverage.md', 'w').write("\n".join(hdr + rows) + "\n")
print("semantics=%d tested=%d untested-with-semantics=%s" % (nsem, ntest, sorted(n for n in NAMES if n in SEM and n not in seen)))
