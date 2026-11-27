#!/usr/bin/env python3
"""CEGAR driver for NOT-gate circuit finding (genfind_not.py encoding).

Solve on a small row set, decode the candidate circuit, check it against
the edge function on ALL 2^n rows, and add only the failing rows
(counterexamples) before re-solving. Design note: PLAN.md 2026-11-27
(L-meta-9809; the full-row NOT encoding OOM'd CaDiCaL at n=14).

- SAT + full verification => circuit found (gate list printed).
- UNSAT on any row subset => GLOBAL UNSAT: no circuit with <= s gates
  exists, because the subset encoding is a relaxation of the full one
  (fewer constraints), so the stated bound is refuted.
- Timeout / iteration cap => INCONCLUSIVE, never a verdict.

Default initial row set: the edge rows (input = exactly one edge's two
endpoints) plus the maximal-independent-set rows. These are the rows a
circuit must already get right to be plausible, and they are few.

Usage: cegar_find_not.py n s EDGES [--init-rows FILE] [--max-iters N]
         [--timeout SECS] [--max-add N] [--workdir DIR] [--cadical PATH]
EDGES as in genfind_not.py (e.g. 01,12,23,03 or 0-1,1-2,2-3,0-3).
Exit codes: 0 = circuit found or GLOBAL UNSAT; 2 = inconclusive.
"""
import argparse
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_CADICAL = os.path.join(os.path.dirname(HERE), "bin", "cadical")
GENFIND = os.path.join(HERE, "genfind_not.py")
DECODE = os.path.join(HERE, "decode_find_not.py")


def parse_edges(espec):
    edges = []
    for tok in espec.split(','):
        if '-' in tok:
            a, b = tok.split('-')
            edges.append((int(a), int(b)))
        else:
            edges.append((int(tok[0]), int(tok[1])))
    return edges


def edge_rows(edges):
    return {(1 << u) | (1 << v) for u, v in edges}


def maximal_independent_set_rows(n, edges):
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    rows = set()
    for r in range(1 << n):
        s = {v for v in range(n) if (r >> v) & 1}
        if any(u in s and v in s for u, v in edges):
            continue
        # maximal iff every vertex outside s has a neighbour in s
        if all(adj[w] & s for w in range(n) if w not in s):
            rows.add(r)
    return rows


def read_rows(path):
    with open(path) as f:
        return sorted({int(t) for t in f.read().replace(',', ' ').split()})


def run_genfind(n, s, espec, rows_path, cnf_path):
    p = subprocess.run([sys.executable, GENFIND, str(n), str(s), espec,
                        cnf_path, '--rows', rows_path],
                       capture_output=True, text=True)
    if p.returncode != 0:
        print(p.stderr, file=sys.stderr)
        raise SystemExit(f'genfind_not.py failed (rc={p.returncode})')
    return p.stderr.strip()


def run_cadical(cadical, cnf_path, proof_path, model_path, timeout):
    with open(model_path, 'w') as mf:
        try:
            p = subprocess.run([cadical, cnf_path, proof_path],
                               stdout=mf, stderr=subprocess.PIPE,
                               text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return 'TIMEOUT', None
    with open(model_path) as f:
        for line in f:
            if line.startswith('s SATISFIABLE'):
                return 'SAT', p.returncode
            if line.startswith('s UNSATISFIABLE'):
                return 'UNSAT', p.returncode
    return 'UNKNOWN', p.returncode


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('n', type=int)
    ap.add_argument('s', type=int)
    ap.add_argument('edges')
    ap.add_argument('--init-rows', default=None,
                    help='file with initial row indices (default: edge rows '
                         '+ maximal-independent-set rows)')
    ap.add_argument('--max-iters', type=int, default=50)
    ap.add_argument('--timeout', type=int, default=300,
                    help='per-solve CaDiCaL cap in seconds')
    ap.add_argument('--max-add', type=int, default=128,
                    help='counterexample rows added per iteration at most')
    ap.add_argument('--workdir', default=None)
    ap.add_argument('--cadical', default=DEFAULT_CADICAL)
    args = ap.parse_args()

    n, s, espec = args.n, args.s, args.edges
    edges = parse_edges(espec)
    if args.init_rows:
        rows = set(read_rows(args.init_rows))
    else:
        rows = edge_rows(edges) | maximal_independent_set_rows(n, edges)
    R = 1 << n
    if any(r < 0 or r >= R for r in rows):
        raise SystemExit(f'init row out of range 0..{R - 1}')

    wd = args.workdir or os.path.join(HERE, 'work', 'find',
                                      f'cegar_{n}_{s}')
    os.makedirs(wd, exist_ok=True)
    rows_path = os.path.join(wd, 'rows.txt')
    cnf_path = os.path.join(wd, 'cegar.cnf')
    model_path = os.path.join(wd, 'model.out')
    proof_path = os.path.join(wd, 'proof.lrat')
    bad_path = os.path.join(wd, 'bad.txt')
    log_path = os.path.join(wd, 'cegar.log')
    log = open(log_path, 'a')

    def note(msg):
        print(msg, flush=True)
        log.write(msg + '\n')
        log.flush()

    note(f'CEGAR n={n} s={s} edges={espec} initial rows={len(rows)} '
         f'max_iters={args.max_iters} timeout={args.timeout}s '
         f'max_add={args.max_add}')
    for it in range(1, args.max_iters + 1):
        with open(rows_path, 'w') as f:
            f.write('\n'.join(map(str, sorted(rows))) + '\n')
        enc = run_genfind(n, s, espec, rows_path, cnf_path)
        t0 = time.time()
        status, _rc = run_cadical(args.cadical, cnf_path, proof_path,
                                  model_path, args.timeout)
        dt = time.time() - t0
        if status == 'TIMEOUT':
            note(f'iter {it}: rows={len(rows)} {enc} solve TIMEOUT '
                 f'after {args.timeout}s -> INCONCLUSIVE (no verdict)')
            log.close()
            return 2
        if status == 'UNKNOWN':
            note(f'iter {it}: rows={len(rows)} {enc} solve {dt:.1f}s '
                 f'-> CaDiCaL gave no status line; INCONCLUSIVE')
            log.close()
            return 2
        if status == 'UNSAT':
            note(f'iter {it}: rows={len(rows)} {enc} solve {dt:.1f}s '
                 f'-> UNSAT on the row subset')
            note(f'CEGAR GLOBAL UNSAT after {it} iteration(s), '
                 f'{len(rows)} rows: no circuit with <= {s} gates exists '
                 f'(subset UNSAT implies full UNSAT)')
            log.close()
            return 0
        # SAT: decode and verify on all rows.
        p = subprocess.run([sys.executable, DECODE, str(n), str(s), espec,
                            model_path, '--bad-rows', bad_path],
                           capture_output=True, text=True)
        if p.returncode == 0:
            note(f'iter {it}: rows={len(rows)} {enc} solve {dt:.1f}s '
                 f'-> SAT, decoded circuit verifies on all {R} rows')
            note(p.stdout.rstrip())
            note(f'CEGAR SUCCESS after {it} iteration(s), '
                 f'{len(rows)} rows used')
            log.close()
            return 0
        bad = read_rows(bad_path)
        new = [r for r in bad if r not in rows]
        if not new:
            note(f'iter {it}: SAT but decoder reports bad rows already '
                 f'in the set ({len(bad)}); INCONCLUSIVE (encoding bug?)')
            log.close()
            return 2
        # Spread the added rows evenly when there are more than max_add,
        # so one iteration does not flood the set with near-identical rows.
        if len(new) > args.max_add:
            step = len(new) / args.max_add
            new = [new[int(k * step)] for k in range(args.max_add)]
        rows |= set(new)
        note(f'iter {it}: rows={len(rows) - len(new)} {enc} solve '
             f'{dt:.1f}s -> SAT, candidate fails on {len(bad)} rows; '
             f'added {len(new)}, now {len(rows)} rows')
    note(f'CEGAR INCONCLUSIVE: max iterations ({args.max_iters}) reached '
         f'with {len(rows)} rows; no verdict')
    log.close()
    return 2


if __name__ == '__main__':
    sys.exit(main())
