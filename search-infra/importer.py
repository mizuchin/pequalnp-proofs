#!/usr/bin/env python3
"""Importer (milestone 3, v1): inline the LRAT library into a generated file.

Takes a genrow/mkrow output that imports PEqualNP.Library.LRAT.Link and
produces a self-contained file: Checker.lean and Link.lean are inlined under
namespace PEqualNP.Outside.<gap>_aux (the L_meta_10000 pattern), and the
generated part keeps its own namespace PEqualNP.Outside.<gap>.

Checker.lean has no imports and no Defs references, so it inlines cleanly.
Link.lean's project imports (Defs.MetaComplexityLgpMono,
MetaComplexity.Helpers.Shannon) are hoisted to the top of the output;
whether a given step may import them depends on that step's desk `imports`.
Usage: importer.py raw.lean GAP checker.lean link.lean out.lean
"""
import re, sys

raw_path, gap, checker_path, link_path, out_path = sys.argv[1:6]
AUX = f"PEqualNP.Outside.{gap}_aux"
LIB = "PEqualNP.Library.LRAT"

def read(p): return open(p).read()

checker = read(checker_path).replace(LIB, AUX)

link = read(link_path)
imports = []
body = []
for line in link.splitlines():
    if line.startswith("import "):
        if "Library.LRAT.Checker" not in line:
            imports.append(line)
        continue
    body.append(line)
link = "\n".join(body).replace(LIB, AUX)

raw = read(raw_path)
raw_lines = [l for l in raw.splitlines() if not l.startswith("import PEqualNP.Library.LRAT")]
raw = "\n".join(raw_lines).replace(LIB, AUX)

out = "\n".join(imports) + "\n\n" + checker.rstrip() + "\n\n" + link.rstrip() + "\n\n" + raw
open(out_path, "w").write(out)
print(f"importer ok: {len(out)} bytes -> {out_path}")
