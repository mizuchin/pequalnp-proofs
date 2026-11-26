#!/usr/bin/env python3
"""Milestone 2: small-scale performance table for the LRAT pipeline.

For each (graph, s): genmono CNF size, CaDiCaL time/result, LRAT size,
generated Lean file size, and Lean build time of the generated file
(local completion proxy per the 2026-11-26 decision). Appends one CSV
row per finished config so a VM replacement loses at most one config.
"""
import csv, os, shutil, subprocess, sys, time

BASE = os.path.expanduser("~/workspace/pequalnp-muse")
REPO = os.path.join(BASE, "pequalnp-proofs")
LRATDIR = os.path.join(REPO, "notes/data/lrat-link")
OUTDIR = os.path.join(BASE, "search-infra/perf")
CSV = os.path.join(OUTDIR, "perf.csv")
CADICAL_TIMEOUT = 900
BUILD_TIMEOUT = 1800

os.makedirs(OUTDIR, exist_ok=True)
env = dict(os.environ)
env["PATH"] = os.path.join(BASE, "bin") + ":" + os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]

def cycle_edges(n):
    return ",".join(f"{i}{(i + 1) % n}" for i in range(n))

CONFIGS = []
for n in range(4, 10):
    for s in (3, 4, 5):
        CONFIGS.append((f"C{n}", n, s, cycle_edges(n)))
    if n >= 7:
        CONFIGS.append((f"C{n}", n, 6, cycle_edges(n)))
CONFIGS.append(("K23", 5, 4, "03,04,12,13,14"))  # milestone-1 anchor

done = set()
if os.path.exists(CSV):
    with open(CSV) as f:
        for row in csv.DictReader(f):
            done.add((row["graph"], int(row["n"]), int(row["s"])))

newfile = not os.path.exists(CSV)
cf = open(CSV, "a", newline="")
w = csv.writer(cf)
if newfile:
    w.writerow(["graph", "n", "s", "edges", "cnf_vars", "cnf_clauses", "cnf_bytes",
                "gen_s", "cadical_s", "cadical_exit", "lrat_bytes", "lean_bytes",
                "segments", "W", "build_s", "build_exit"])
    cf.flush()

def run(cmd, timeout, **kw):
    t = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env, **kw)
        return time.time() - t, r
    except subprocess.TimeoutExpired:
        return time.time() - t, None

for graph, n, s, edges in CONFIGS:
    if (graph, n, s) in done:
        print(f"skip {graph} n={n} s={s}", flush=True)
        continue
    tag = f"{graph}_{n}_{s}"
    work = os.path.join(OUTDIR, "work", tag)
    os.makedirs(work, exist_ok=True)
    cnf = os.path.join(work, "row.cnf"); lrat = os.path.join(work, "row.lrat")
    out = os.path.join(work, "row.lean")
    # genmono
    gt, r = run([sys.executable, os.path.join(LRATDIR, "genmono.py"), str(n), str(s), edges, cnf, "rows"], 300)
    if r is None or r.returncode != 0:
        print(f"{tag}: genmono failed", flush=True); continue
    hdr = open(cnf).readline().split()
    cvars, cclauses = int(hdr[2]), int(hdr[3])
    rows = r.stderr.split("rows [")[1].split("]")[0].replace(" ", "")
    # cadical
    ct, r = run(["cadical", "-q", "--unsat", "--seed=2", "--lrat", "--no-binary", cnf, lrat], CADICAL_TIMEOUT)
    cexit = "timeout" if r is None else r.returncode
    lrat_bytes = os.path.getsize(lrat) if os.path.exists(lrat) else ""
    lean_bytes = segments = W = build_s = build_exit = ""
    if r is not None and r.returncode == 20:
        fx = " || ".join(f"(x {e[0]} && x {e[1]})" for e in edges.split(","))
        _, r2 = run([sys.executable, os.path.join(LRATDIR, "genrow.py"), cnf, lrat, out,
                     "PEqualNP.Outside.L_perf_tmp", str(n), str(s), rows, fx, "--seg", "60000"], 600)
        if r2 is not None and r2.returncode == 0:
            lean_bytes = os.path.getsize(out)
            tail = (r2.stdout + r2.stderr).replace(",", " ")
            for part in tail.split():
                if part.startswith("segments="): segments = part.split("=")[1]
                if part.startswith("W="): W = part.split("=")[1]
            # build in tree
            dest = os.path.join(REPO, "lean/PEqualNP/Outside/L_perf_tmp.lean")
            shutil.copy(out, dest)
            bt, r3 = run(["lake", "build", "PEqualNP.Outside.L_perf_tmp"], BUILD_TIMEOUT, cwd=os.path.join(REPO, "lean"))
            build_s = f"{bt:.1f}"
            build_exit = "timeout" if r3 is None else r3.returncode
            os.unlink(dest)
    w.writerow([graph, n, s, edges, cvars, cclauses, os.path.getsize(cnf), f"{gt:.2f}",
                f"{ct:.2f}", cexit, lrat_bytes, lean_bytes, segments, W, build_s, build_exit])
    cf.flush()
    print(f"done {tag}: clauses={cclauses} cadical={ct:.1f}s exit={cexit} lean={lean_bytes} build={build_s}", flush=True)

print("ALL DONE", flush=True)
