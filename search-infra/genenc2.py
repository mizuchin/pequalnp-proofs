#!/usr/bin/env python3
"""CNF of the enc2 encoding (Defs.LratEncoding.enc2 = enc part in the
(s+1)-stride layout + fLex) for an edge function on all rows.
Adapted from genpromise.py (same code, full row set, edge predicate).

Usage: genenc2.py n s EDGES out.cnf
"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
edges = [(int(e[0]), int(e[1])) for e in sys.argv[3].split(',')]
out = sys.argv[4]
N = n
R = 1 << N
A = R + N + s + 1
ROWS = list(range(R))
def g(r): return any((r >> u) & 1 and (r >> v) & 1 for u, v in edges)
def ix(kd, j, a): return (kd * (s + 1) + j) * A + a
def P(v): return v + 1
def Q(v): return -(v + 1)
def L(v, b): return P(v) if b else Q(v)
def bit(r, k): return (r >> k) & 1 == 1
F = []
# fOp
for j in range(s): F.append([P(ix(0, j, 0)), P(ix(0, j, 1)), P(ix(0, j, 2))])
# fSrcAlo
for sd in (1, 2):
    for j in range(s): F.append([P(ix(sd, j, k)) for k in range(N + j + 1)])
# fSrcEq
for sd in (1, 2):
    for j in range(s):
        for r in ROWS:
            for k in range(N + j + 1):
                if k < N: F.append([Q(ix(sd, j, k)), L(ix(sd + 3, j, r), bit(r, k))])
                elif k < N + j:
                    F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r)), P(ix(3, k - N, r))])
                    F.append([Q(ix(sd, j, k)), P(ix(sd + 3, j, r)), Q(ix(3, k - N, r))])
                else: F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r))])
# fGate
for j in range(s):
    for r in ROWS:
        o0, o1, o2 = ix(0, j, 0), ix(0, j, 1), ix(0, j, 2)
        w, u1, u2 = ix(3, j, r), ix(4, j, r), ix(5, j, r)
        F += [[Q(o0), Q(w), P(u1)], [Q(o0), Q(w), P(u2)], [Q(o0), P(w), Q(u1), Q(u2)],
              [Q(o1), P(w), Q(u1)], [Q(o1), P(w), Q(u2)], [Q(o1), Q(w), P(u1), P(u2)],
              [Q(o2), P(w)]]
# fOutAlo
F.append([P(ix(6, 0, k)) for k in range(N + s + 1)])
# fOutEq
for r in ROWS:
    for k in range(N + s + 1):
        if k < N:
            if bit(r, k) != g(r): F.append([Q(ix(6, 0, k))])
        elif k < N + s: F.append([Q(ix(6, 0, k)), L(ix(3, k - N, r), g(r))])
        elif g(r): F.append([Q(ix(6, 0, k))])
# normal form
pad = lambda j: ix(7, j, 0)
if s > 0:
    F.append([P(ix(6, 0, N + s - 1)), P(pad(s - 1))])
for j in range(s):
    F += [[Q(pad(j)), P(ix(0, j, 2))], [Q(pad(j)), P(ix(1, j, N + j))], [Q(pad(j)), P(ix(2, j, N + j))],
          [P(pad(j)), Q(ix(0, j, 2))], [P(pad(j)), Q(ix(1, j, N + j))], [P(pad(j)), Q(ix(2, j, N + j))]]
for j in range(s - 1): F.append([Q(pad(j + 1)), P(pad(j))])
for j in range(s):
    for i in range(j):
        F += [[Q(pad(i)), Q(ix(1, j, N + i))], [Q(pad(i)), Q(ix(2, j, N + i))]]
for j in range(s):
    for k in range(N + j + 1):
        for l in range(k + 1):
            F.append([Q(ix(1, j, k)), Q(ix(2, j, l)), P(pad(j))])
for j in range(s - 1):
    F.append([P(ix(1, i, N + j)) for i in range(j + 1, s)] + [P(ix(2, i, N + j)) for i in range(j + 1, s)] + [P(pad(j))])
# fLex
for j in range(s - 1):
    base = [P(pad(j)), P(ix(1, j + 1, N + j)), P(ix(2, j + 1, N + j))]
    for a in range(N + j + 1):
        for b in range(a):
            F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, b))] + base)
        for c in range(N + j + 1):
            for d in range(c):
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, d))] + base)
            F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j, 1))] + base)
            F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j + 1, 0))] + base)
nv = 10 * (s + 1) * A
with open(out, 'w') as o:
    o.write(f'p cnf {nv} {len(F)}\n')
    for c in F: o.write(' '.join(map(str, c)) + ' 0\n')
print(f'vars={nv} clauses={len(F)} rows={ROWS}', file=sys.stderr)
