#!/usr/bin/env python3
"""CNF for circuit FINDING with NOT gates: exists an AND/OR/NOT circuit
(fan-in <= 2, every gate counted) with <= s gates computing the edge
function of a graph on n vertices (input = vertex indicators, output =
some listed edge has both ends true). genfind.py's encoding plus a 4th
op value (3 = NOT, reads source 1 only). Padding (op 2) makes the fixed
s slots mean "at most s". Full 2^n rows (NOT breaks the monotone row
reduction). Clauses are streamed to the file (the instances are large).

Usage: genfind_not.py n s EDGES out.cnf [--rows FILE|LIST]
EDGES like 08,010,17 (vertex numbers concatenated, each < 10) or
u-v pairs separated by commas: 0-8,0-10,1-7.
--rows restricts the encoded rows: a file with one row index per line
(commas/whitespace also accepted), or a comma-separated list of row
indices. Default: all 2^n rows. The variable layout is unchanged, so
decode_find_not.py still applies. Used by cegar_find_not.py (CEGAR).
"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
espec = sys.argv[3]
out = sys.argv[4]
edges = []
for tok in espec.split(','):
    if '-' in tok:
        a, b = tok.split('-'); edges.append((int(a), int(b)))
    else:
        edges.append((int(tok[0]), int(tok[1])))
R = 1 << n
A = R + n + s + 1
# Row subset (CEGAR): default all rows; --rows FILE|LIST restricts the
# row-dependent clauses (source wiring, gate evaluation, output) to the
# given rows. Structural clauses are row-independent and unchanged.
rows = list(range(R))
i = 5
while i < len(sys.argv):
    if sys.argv[i] == '--rows' and i + 1 < len(sys.argv):
        import os
        spec = sys.argv[i + 1]
        txt = open(spec).read() if os.path.isfile(spec) else spec
        rows = sorted({int(t) for t in txt.replace(',', ' ').split()})
        bad = [r for r in rows if r < 0 or r >= R]
        if bad:
            raise SystemExit(f'row out of range 0..{R - 1}: {bad[:5]}')
        i += 2
    else:
        raise SystemExit(f'unknown argument: {sys.argv[i]}')
def g(r): return any((r >> u) & 1 and (r >> v) & 1 for u, v in edges)
def ix(kd, j, a): return (kd * (s + 1) + j) * A + a
def P(v): return v + 1
def Q(v): return -(v + 1)
def L(v, b): return P(v) if b else Q(v)
def bit(r, k): return (r >> k) & 1 == 1

def clauses():
    for j in range(s):
        yield [P(ix(0, j, t)) for t in range(4)]
    for sd in (1, 2):
        for j in range(s):
            yield [P(ix(sd, j, k)) for k in range(n + j + 1)]
    for sd in (1, 2):
        for j in range(s):
            for r in rows:
                for k in range(n + j + 1):
                    if k < n:
                        yield [Q(ix(sd, j, k)), L(ix(sd + 3, j, r), bit(r, k))]
                    elif k < n + j:
                        yield [Q(ix(sd, j, k)), Q(ix(sd + 3, j, r)), P(ix(3, k - n, r))]
                        yield [Q(ix(sd, j, k)), P(ix(sd + 3, j, r)), Q(ix(3, k - n, r))]
                    else:
                        yield [Q(ix(sd, j, k)), Q(ix(sd + 3, j, r))]
    for j in range(s):
        for r in rows:
            o0, o1, o2, o3 = ix(0, j, 0), ix(0, j, 1), ix(0, j, 2), ix(0, j, 3)
            w, u1, u2 = ix(3, j, r), ix(4, j, r), ix(5, j, r)
            yield [Q(o0), Q(w), P(u1)]; yield [Q(o0), Q(w), P(u2)]; yield [Q(o0), P(w), Q(u1), Q(u2)]
            yield [Q(o1), P(w), Q(u1)]; yield [Q(o1), P(w), Q(u2)]; yield [Q(o1), Q(w), P(u1), P(u2)]
            yield [Q(o2), P(w)]
            yield [Q(o3), Q(w), Q(u1)]; yield [Q(o3), P(w), P(u1)]
    yield [P(ix(6, 0, k)) for k in range(n + s + 1)]
    for r in rows:
        gr = g(r)
        for k in range(n + s + 1):
            if k < n:
                if bit(r, k) != gr: yield [Q(ix(6, 0, k))]
            elif k < n + s:
                yield [Q(ix(6, 0, k)), L(ix(3, k - n, r), gr)]
            elif gr:
                yield [Q(ix(6, 0, k))]
    pad = lambda j: ix(7, j, 0)
    yield [P(ix(6, 0, n + s - 1)), P(pad(s - 1))]
    for j in range(s):
        yield [Q(pad(j)), P(ix(0, j, 2))]; yield [Q(pad(j)), P(ix(1, j, n + j))]; yield [Q(pad(j)), P(ix(2, j, n + j))]
        yield [P(pad(j)), Q(ix(0, j, 2))]; yield [P(pad(j)), Q(ix(1, j, n + j))]; yield [P(pad(j)), Q(ix(2, j, n + j))]
    for j in range(s - 1):
        yield [Q(pad(j + 1)), P(pad(j))]
    for j in range(s):
        for i in range(j):
            yield [Q(pad(i)), Q(ix(1, j, n + i))]
            yield [Q(pad(i)), Q(ix(2, j, n + i))]
    for j in range(s):
        for k in range(n + j + 1):
            for l in range(k + 1):
                yield [Q(ix(1, j, k)), Q(ix(2, j, l)), P(pad(j))]
    for j in range(s - 1):
        yield [P(ix(1, i, n + j)) for i in range(j + 1, s)] + [P(ix(2, i, n + j)) for i in range(j + 1, s)] + [P(pad(j))]

nv = 10 * (s + 1) * A
tmp = out + '.body'
cnt = 0
with open(tmp, 'w') as o:
    for c in clauses():
        o.write(' '.join(map(str, c)) + ' 0\n')
        cnt += 1
with open(out, 'w') as o:
    o.write(f'p cnf {nv} {cnt}\n')
    with open(tmp) as t:
        while True:
            chunk = t.read(1 << 22)
            if not chunk: break
            o.write(chunk)
import os
os.remove(tmp)
print(f'rows={len(rows)} vars={nv} clauses={cnt}', file=sys.stderr)
