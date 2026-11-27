#!/usr/bin/env python3
"""Decode a CaDiCaL model of genfind.py into a circuit: prune padding and
unreachable gates, renumber wires, verify the circuit against the truth
table on every row (root semantics), and print the Lean gate list.

Usage: decode_find.py n s TABLE model.out
TABLE as in genfind.py.
"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
tspec = sys.argv[3]
R = 1 << n
A = R + n + s + 1
if tspec.startswith("0x"):
    table = int(tspec, 16)
    def g(r): return (table >> r) & 1 == 1
else:
    tset = {int(x) for x in tspec.split(',') if x != ''}
    def g(r): return r in tset
val = set()
for line in open(sys.argv[4]):
    if line.startswith('v'):
        val |= {int(x) for x in line.split()[1:] if int(x) > 0}
def T(kd, j, a): return ((kd * (s + 1) + j) * A + a + 1) in val
gates = []  # slot j -> (op, [inputs]) with op in {'and','or','const'}
for j in range(s):
    op = [t for t in range(3) if T(0, j, t)]
    s1 = [k for k in range(n + j + 1) if T(1, j, k)]
    s2 = [k for k in range(n + j + 1) if T(2, j, k)]
    assert op and s1 and s2
    if op[0] == 2: gates.append(('const', []))
    else: gates.append((['and', 'or'][op[0]], [s1[0], s2[0]]))
so = [k for k in range(n + s + 1) if T(6, 0, k)]
assert so
out_wire = so[0]
# prune to gates reachable from the output wire, renumber in slot order
reach = set()
def mark(w):
    if w >= n and w - n not in reach:
        reach.add(w - n)
        for i in gates[w - n][1]: mark(i)
mark(out_wire)
order = sorted(reach)
remap = {old: n + i for i, old in enumerate(order)}
def xlate(w):
    return w if w < n else remap[w - n]
new_gates = []
for old in order:
    op, ins = gates[old]
    new_gates.append((op, [xlate(i) for i in ins]))
new_out = xlate(out_wire)
# verify on all rows (root semantics: missing wire reads false)
def evaluate(r):
    w = [(r >> i) & 1 == 1 for i in range(n)]
    for op, ins in new_gates:
        v = [w[i] if i < len(w) else False for i in ins]
        w.append(True if op == 'const' else (all(v) if op == 'and' else any(v)))
    return w[new_out] if new_out < len(w) else False
bad = [r for r in range(R) if evaluate(r) != g(r)]
if bad:
    print(f"VERIFY FAILED on {len(bad)} rows, e.g. {bad[:5]}")
    sys.exit(1)
print(f"verified: {len(new_gates)} gates, output wire {new_out}, all {R} rows match")
for j, (op, ins) in enumerate(new_gates):
    print(f"w{n + j} = {op}{ins}")
gs = ", ".join(
    "⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩" if op == 'const'
    else f"⟨PEqualNP.CircuitLowerBounds.GateOp.{op}, [{ins[0]}, {ins[1]}]⟩"
    for op, ins in new_gates)
print(f"lean gates: [{gs}], output {new_out}")
