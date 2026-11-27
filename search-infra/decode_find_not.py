#!/usr/bin/env python3
"""Decode a CaDiCaL model of genfind_not.py into an AND/OR/NOT circuit:
prune padding/unreachable gates, renumber, verify against the edge
function on every row (root semantics), print the gate list.

Usage: decode_find_not.py n s EDGES model.out [--bad-rows FILE]
[--bad-rows FILE] writes every failing row index (one per line) to FILE
when verification fails; used by cegar_find_not.py to collect
counterexamples. Without it the behaviour is unchanged.
"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
espec = sys.argv[3]
edges = []
for tok in espec.split(','):
    if '-' in tok:
        a, b = tok.split('-'); edges.append((int(a), int(b)))
    else:
        edges.append((int(tok[0]), int(tok[1])))
R = 1 << n
A = R + n + s + 1
def g(r): return any((r >> u) & 1 and (r >> v) & 1 for u, v in edges)
val = set()
for line in open(sys.argv[4]):
    if line.startswith('v'):
        val |= {int(x) for x in line.split()[1:] if int(x) > 0}
def T(kd, j, a): return ((kd * (s + 1) + j) * A + a + 1) in val
gates = []
for j in range(s):
    op = [t for t in range(4) if T(0, j, t)]
    s1 = [k for k in range(n + j + 1) if T(1, j, k)]
    s2 = [k for k in range(n + j + 1) if T(2, j, k)]
    assert op and s1 and s2, f"gate {j} incomplete"
    if op[0] == 2: gates.append(('const', []))
    elif op[0] == 3: gates.append(('not', [s1[0]]))
    else: gates.append((['and', 'or'][op[0]], [s1[0], s2[0]]))
so = [k for k in range(n + s + 1) if T(6, 0, k)]
assert so
out_wire = so[0]
reach = set()
def mark(w):
    if w >= n and w - n not in reach:
        reach.add(w - n)
        for i in gates[w - n][1]: mark(i)
mark(out_wire)
order = sorted(reach)
remap = {old: n + i for i, old in enumerate(order)}
def xlate(w): return w if w < n else remap[w - n]
new_gates = []
for old in order:
    op, ins = gates[old]
    new_gates.append((op, [xlate(i) for i in ins]))
new_out = xlate(out_wire)
def evaluate(r):
    w = [(r >> i) & 1 == 1 for i in range(n)]
    for op, ins in new_gates:
        v = [w[i] if i < len(w) else False for i in ins]
        if op == 'const': w.append(True)
        elif op == 'not': w.append(not v[0])
        elif op == 'and': w.append(all(v))
        else: w.append(any(v))
    return w[new_out] if new_out < len(w) else False
bad = [r for r in range(R) if evaluate(r) != g(r)]
if bad:
    print(f"VERIFY FAILED on {len(bad)} rows, e.g. {bad[:5]}")
    if '--bad-rows' in sys.argv:
        with open(sys.argv[sys.argv.index('--bad-rows') + 1], 'w') as f:
            f.write('\n'.join(map(str, bad)) + '\n')
    sys.exit(1)
print(f"verified: {len(new_gates)} gates, output wire {new_out}, all {R} rows match")
for j, (op, ins) in enumerate(new_gates):
    print(f"w{n + j} = {op}{ins}")
