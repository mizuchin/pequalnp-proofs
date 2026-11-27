#!/usr/bin/env python3
"""Decode a CaDiCaL model of genpromise.py (enc2 layout) into a circuit:
prune padding/unreachable gates, renumber, verify against the mask M on
all unit rows (root semantics), print the Lean gate list.

Usage: decode_promise.py n m M s model.out
"""
import sys
n, m, M, s = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
N = n + m
R = 1 << N
A = R + N + s + 1
val = set()
for line in open(sys.argv[5]):
    if line.startswith('v'):
        val |= {int(x) for x in line.split()[1:] if int(x) > 0}
def T(kd, j, a): return ((kd * (s + 1) + j) * A + a + 1) in val
gates = []
for j in range(s):
    op = [t for t in range(3) if T(0, j, t)]
    s1 = [k for k in range(N + j + 1) if T(1, j, k)]
    s2 = [k for k in range(N + j + 1) if T(2, j, k)]
    assert op and s1 and s2, f"gate {j} incomplete"
    if op[0] == 2: gates.append(('const', []))
    else: gates.append((['and', 'or'][op[0]], [s1[0], s2[0]]))
so = [k for k in range(N + s + 1) if T(6, 0, k)]
assert so
out_wire = so[0]
reach = set()
def mark(w):
    if w >= N and w - N not in reach:
        reach.add(w - N)
        for i in gates[w - N][1]: mark(i)
mark(out_wire)
order = sorted(reach)
remap = {old: N + i for i, old in enumerate(order)}
def xlate(w): return w if w < N else remap[w - N]
new_gates = []
for old in order:
    op, ins = gates[old]
    new_gates.append((op, [xlate(i) for i in ins]))
new_out = xlate(out_wire)
def evaluate(r):
    w = [(r >> i) & 1 == 1 for i in range(N)]
    for op, ins in new_gates:
        v = [w[i] if i < len(w) else False for i in ins]
        w.append(True if op == 'const' else (all(v) if op == 'and' else any(v)))
    return w[new_out] if new_out < len(w) else False
bad = []
for u in range(n):
    for v in range(m):
        row = (1 << u) + (1 << (n + v))
        if evaluate(row) != ((M >> (m * u + v)) & 1 == 1): bad.append((u, v))
if bad:
    print(f"VERIFY FAILED on {len(bad)} unit rows, e.g. {bad[:5]}")
    sys.exit(1)
print(f"verified: {len(new_gates)} gates, output wire {new_out}, all {n * m} unit rows match M={M}")
for j, (op, ins) in enumerate(new_gates):
    print(f"w{N + j} = {op}{ins}")
gs = ", ".join(
    "⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩" if op == 'const'
    else f"⟨PEqualNP.CircuitLowerBounds.GateOp.{op}, [{ins[0]}, {ins[1]}]⟩"
    for op, ins in new_gates)
print(f"lean gates: [{gs}], output {new_out}")
