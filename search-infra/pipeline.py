#!/usr/bin/env python3
"""End-to-end pipeline for A-type steps (milestone 3 wiring).

Input: gap id + the exact posted statement text.
Chain: classify -> parse (n, s, edges) -> mkrow -> importer (inline LRAT)
-> shape (set_option `in` form + final theorem with the exact statement)
-> size check (512 KiB) -> place in tree -> outside-guard (gap-of-file,
imports, closure) -> lake build -> remove.
Usage: pipeline.py GAP statement.txt [--keep] [--imports M1,M2,...]
The guard's listed imports default to ["PEqualNP.Defs"]; pass --imports
with the desk row's list when it differs.
The final theorem is proved from the generated `lower`; a ReadsBack
hypothesis (classifier: droppable side condition) is introduced and ignored.
Usage: pipeline.py GAP statement.txt [--keep]
"""
import json, os, re, shutil, subprocess, sys

BASE = os.path.expanduser("~/workspace/pequalnp-muse")
REPO = os.path.join(BASE, "pequalnp-proofs")
SI = os.path.join(BASE, "search-infra")
sys.path.insert(0, SI)
from classify import classify

gap, stmt_path = sys.argv[1], sys.argv[2]
keep = "--keep" in sys.argv
listed_imports = ["PEqualNP.Defs"]
if "--imports" in sys.argv:
    listed_imports = sys.argv[sys.argv.index("--imports") + 1].split(",")
stmt = " ".join(open(stmt_path).read().split())
cls, reasons = classify(stmt)
print(f"classify: {cls} | {'; '.join(reasons)}", flush=True)
if cls not in ("A", "L"):
    sys.exit(f"pipeline handles A and L only (got {cls})")
link_mode = cls == "L"
if link_mode:
    encm = (re.search(r"\benc\s*\(\s*(\d+)\s*:\s*ℕ\s*\)\s*\(\s*(\d+)\s*:\s*ℕ\s*\)", stmt)
            or re.search(r"\benc\s+(\d+)\s+(\d+)\b", stmt))
    n, s = int(encm.group(1)), int(encm.group(2))
    print(f"parsed (link): n={n} s={s}", flush=True)
else:
    n = int(re.search(r"Fin (\d+) → Bool", stmt).group(1))
    bound = int(re.search(r"(\d+)\s*≤\s*\S+\.size\b", stmt).group(1))
    s = bound - 1
    edges = [(a, b) for a, b in re.findall(r"z (\d+) && z (\d+)", stmt)]
    edges_str = ",".join(f"{a}{b}" for a, b in edges)
    readsback = any("ReadsBack" in r for r in reasons)
    print(f"parsed: n={n} s={s} edges={edges_str} readsback={readsback}", flush=True)

work = os.path.join(SI, "work", "pipeline", gap)
os.makedirs(work, exist_ok=True)
env = dict(os.environ)
env["PATH"] = os.path.join(BASE, "bin") + ":" + os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]

def run(cmd, **kw):
    print("+", " ".join(cmd), flush=True)
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, **kw)
    if r.returncode != 0:
        print(r.stdout[-2000:]); print(r.stderr[-2000:])
        sys.exit(f"FAILED ({r.returncode}): {cmd[0]}")
    return r

raw = os.path.join(work, "raw.lean")
if link_mode:
    open(raw, "w").write("")  # no generated part: the proof is Link specialized
else:
    run([sys.executable, "mkrow.py", str(n), str(s), edges_str, raw, f"PEqualNP.Outside.{gap}",
         "--work", os.path.join(work, "cache")],
        cwd=os.path.join(REPO, "notes/data/lrat-link"))
inlined = os.path.join(work, "inlined.lean")
run([sys.executable, os.path.join(SI, "importer.py"), raw, gap,
     os.path.join(REPO, "lean/PEqualNP/Library/LRAT/Checker.lean"),
     os.path.join(REPO, "lean/PEqualNP/Library/LRAT/Link.lean"),
     os.path.join(REPO, "lean/PEqualNP/MetaComplexity/Helpers/Shannon.lean"), inlined])

src = open(inlined).read()
if link_mode:
    aux = f"PEqualNP.Outside.{gap}_aux.Link"
    final = (f"\ntheorem PEqualNP.Outside.{gap} : {stmt} := by\n"
             f"  intro rows g C bounded monotone small agrees\n"
             f"  have valid := {aux}.valid_ofCirc {n} {s} g (· ∈ rows) C monotone small agrees\n"
             f"  obtain ⟨M, hv, normal⟩ := {aux}.exists_nf ⟨_, valid⟩\n"
             f"  exact ⟨{aux}.val {n} {s} M, {aux}.enc_sat bounded hv normal⟩\n")
else:
    src = src.replace("set_option maxRecDepth 1000000\n", "")
    src = src.replace("set_option maxHeartbeats 0\n", "")
    src = src.replace("theorem unsat",
                      "set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 0 in\ntheorem unsat", 1)
    lam = "fun C hm hr he => " if readsback else "fun C hm he => "
    final = (f"\ntheorem PEqualNP.Outside.{gap} : {stmt} :=\n"
             f"  {lam}PEqualNP.Outside.{gap}.lower C hm he\n")
src = src.rstrip() + "\n" + final
out = os.path.join(work, f"{gap}.lean")
open(out, "w").write(src)
size = os.path.getsize(out)
print(f"shaped: {size} bytes (limit 524288: {'OK' if size <= 524288 else 'OVER'})", flush=True)
if size > 524288:
    sys.exit("file exceeds 512 KiB")

dest = os.path.join(REPO, f"lean/PEqualNP/Outside/{gap}.lean")
backup = None
if os.path.exists(dest):
    backup = os.path.join(work, "original.lean"); shutil.copy(dest, backup)
shutil.copy(out, dest)
try:
    rel = f"lean/PEqualNP/Outside/{gap}.lean"
    gout = os.path.join(work, "guard")
    os.makedirs(gout, exist_ok=True)
    gap_id = "L-" + gap[2:].replace("_", "-") if gap.startswith("L_") else gap
    gaps_json = os.path.join(work, "gaps.json")
    with open(gaps_json, "w") as fh:
        json.dump({"gaps": [{"id": gap_id, "file": rel,
                             "module": f"PEqualNP.Outside.{gap}",
                             "statement": stmt, "imports": listed_imports,
                             "kind": "check"}]}, fh)
    guard = os.path.join(REPO, ".github/scripts/outside-guard.mjs")
    run(["node", guard, "gap-of-file", gaps_json, rel, gout], cwd=REPO)
    run(["node", guard, "imports", rel, os.path.join(gout, "imports.json"), rel], cwd=REPO)
    run(["node", guard, "closure", ".", os.path.join(gout, "imports.json"), rel, gout], cwd=REPO)
    print("GUARD OK", flush=True)
    r = subprocess.run(["lake", "build", f"PEqualNP.Outside.{gap}"],
                       capture_output=True, text=True, env=env, cwd=os.path.join(REPO, "lean"))
    print("build exit:", r.returncode, flush=True)
    if r.returncode != 0:
        print((r.stdout + r.stderr)[-3000:])
        sys.exit("BUILD FAILED")
finally:
    if backup: shutil.copy(backup, dest)
    elif not keep: os.unlink(dest)
print("PIPELINE OK", flush=True)
