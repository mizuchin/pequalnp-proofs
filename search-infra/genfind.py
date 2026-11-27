#!/usr/bin/env python3
"""CNF for circuit FINDING (upper side): exists a Monotone2 circuit with
<= s gates computing a given truth table on n inputs. This is genmono.py's
encoding with the edge predicate replaced by an arbitrary table and all
rows kept (no monotone row reduction), so non-monotone tables are fine as
long as an AND/OR circuit exists. Padding (op 2 = constant true) makes
the fixed s slots mean "at most s".

Usage: genfind.py n s TABLE out.cnf [--lex]
TABLE: comma-separated true rows ("3,5,6,7") or a 0x... bitmask
(bit r = value on row r). --lex adds the fLex symmetry clauses.
"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
tspec = sys.argv[3]
out = sys.argv[4]
use_lex = "--lex" in sys.argv[5:]
mono = "--mono" in sys.argv[5:]
R = 1 << n
A = R + n + s + 1
if tspec.startswith("0x"):
    table = int(tspec, 16)
    def g(r): return (table >> r) & 1 == 1
else:
    tset = {int(x) for x in tspec.split(',') if x != ''}
    def g(r): return r in tset
if mono:
    # valid only for monotone tables: a monotone circuit is determined by
    # the minimal true rows and the maximal false rows
    T = [r for r in range(R) if g(r)]; N = [r for r in range(R) if not g(r)]
    for r in T:
        for k in range(n):
            if not (r >> k) & 1:
                assert g(r | (1 << k)), "table is not monotone"
    mint = [r for r in T if not any(q != r and q & r == q for q in T)]
    maxf = [r for r in N if not any(q != r and q & r == r for q in N)]
    ROWS = sorted(mint + maxf)
    print(f'mono rows: {len(ROWS)} (mint {len(mint)} + maxf {len(maxf)}) of {R}', file=sys.stderr)
else:
    ROWS = list(range(R))
def ix(kd, j, a): return (kd * (s + 1) + j) * A + a
def P(v): return v + 1
def Q(v): return -(v + 1)
def L(v, b): return P(v) if b else Q(v)
def bit(r, k): return (r >> k) & 1 == 1
F = []
for j in range(s): F.append([P(ix(0, j, 0)), P(ix(0, j, 1)), P(ix(0, j, 2))])
for sd in (1, 2):
    for j in range(s): F.append([P(ix(sd, j, k)) for k in range(n + j + 1)])
for sd in (1, 2):
    for j in range(s):
        for r in ROWS:
            for k in range(n + j + 1):
                if k < n: F.append([Q(ix(sd, j, k)), L(ix(sd + 3, j, r), bit(r, k))])
                elif k < n + j:
                    F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r)), P(ix(3, k - n, r))])
                    F.append([Q(ix(sd, j, k)), P(ix(sd + 3, j, r)), Q(ix(3, k - n, r))])
                else: F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r))])
for j in range(s):
    for r in ROWS:
        o0, o1, o2 = ix(0, j, 0), ix(0, j, 1), ix(0, j, 2)
        w, u1, u2 = ix(3, j, r), ix(4, j, r), ix(5, j, r)
        F += [[Q(o0), Q(w), P(u1)], [Q(o0), Q(w), P(u2)], [Q(o0), P(w), Q(u1), Q(u2)],
              [Q(o1), P(w), Q(u1)], [Q(o1), P(w), Q(u2)], [Q(o1), Q(w), P(u1), P(u2)],
              [Q(o2), P(w)]]
F.append([P(ix(6, 0, k)) for k in range(n + s + 1)])
for r in ROWS:
    for k in range(n + s + 1):
        if k < n:
            if bit(r, k) != g(r): F.append([Q(ix(6, 0, k))])
        elif k < n + s: F.append([Q(ix(6, 0, k)), L(ix(3, k - n, r), g(r))])
        elif g(r): F.append([Q(ix(6, 0, k))])
pad = lambda j: ix(7, j, 0)
F.append([P(ix(6, 0, n + s - 1)), P(pad(s - 1))])
for j in range(s):
    F += [[Q(pad(j)), P(ix(0, j, 2))], [Q(pad(j)), P(ix(1, j, n + j))], [Q(pad(j)), P(ix(2, j, n + j))],
          [P(pad(j)), Q(ix(0, j, 2))], [P(pad(j)), Q(ix(1, j, n + j))], [P(pad(j)), Q(ix(2, j, n + j))]]
for j in range(s - 1): F.append([Q(pad(j + 1)), P(pad(j))])
for j in range(s):
    for i in range(j):
        F += [[Q(pad(i)), Q(ix(1, j, n + i))], [Q(pad(i)), Q(ix(2, j, n + i))]]
for j in range(s):
    for k in range(n + j + 1):
        for l in range(k + 1):
            F.append([Q(ix(1, j, k)), Q(ix(2, j, l)), P(pad(j))])
for j in range(s - 1):
    F.append([P(ix(1, i, n + j)) for i in range(j + 1, s)] + [P(ix(2, i, n + j)) for i in range(j + 1, s)] + [P(pad(j))])
if use_lex:
    for j in range(s - 1):
        base = [P(pad(j)), P(ix(1, j + 1, n + j)), P(ix(2, j + 1, n + j))]
        for a in range(n + j + 1):
            for b in range(a):
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, b))] + base)
            for c in range(n + j + 1):
                for d in range(c):
                    F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, d))] + base)
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j, 1))] + base)
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j + 1, 0))] + base)
nv = 10 * (s + 1) * A
with open(out, 'w') as o:
    o.write(f'p cnf {nv} {len(F)}\n')
    for c in F: o.write(' '.join(map(str, c)) + ' 0\n')
print(f'vars={nv} clauses={len(F)}', file=sys.stderr)
