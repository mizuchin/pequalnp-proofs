#!/usr/bin/env python3
"""Importer (milestone 3, v2): inline the LRAT library into a generated file,
outside-guard clean.

Takes a genrow/mkrow output that imports PEqualNP.Library.LRAT.Link and
produces a self-contained file: Checker.lean and Link.lean are inlined under
namespace PEqualNP.Outside.<gap>_aux (the L_meta_10000 pattern), and the
generated part keeps its own namespace PEqualNP.Outside.<gap>.

Guard compliance (outside-guard.mjs scans the raw text, comments included):
- all comments are stripped from the inlined library parts;
- Link.lean's `macro "wdt"` is deleted and its 13 uses, all of the form
  `simp (disch := wdt)`, are replaced by the macro's expansion
  `(first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))`;
- imports are NOT hoisted from Link.lean. The only import emitted is
  `import PEqualNP.Defs` (Link's MetaComplexityLgpMono lives under the Defs
  root). Shannon is outside the Defs root, so the wire-fold lemmas Link
  actually uses (wiresFrom, wires_eq, wiresFrom_append, wiresFrom_prefix,
  length_wiresFrom, getD_wiresFrom) are copied into the aux namespace,
  the L_meta_3644 pattern, and `PEqualNP.MetaComplexity.Helpers` is dropped
  from Link's `open` line.
Usage: importer.py raw.lean GAP checker.lean link.lean shannon.lean out.lean
"""
import re, sys

raw_path, gap, checker_path, link_path, shannon_path, out_path = sys.argv[1:7]
AUX = f"PEqualNP.Outside.{gap}_aux"
LIB = "PEqualNP.Library.LRAT"

def read(p): return open(p).read()

def strip_comments(src):
    """Remove Lean comments: nested /- -/ blocks (incl. /-- and /-!) and
    -- line comments. String literals are tracked so markers inside them
    are left alone; callers assert none survive in library code."""
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i): depth += 1; i += 2
            elif src.startswith("-/", i): depth -= 1; i += 2
            else: i += 1
            continue
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1]); i += 2; continue
            if c == '"': in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True; out.append(c); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n": i += 1
            continue
        out.append(c); i += 1
    # collapse runs of blank lines left by stripped block comments
    return re.sub(r"\n{3,}", "\n\n", "".join(out))

def shannon_block(src):
    """The wire-fold block of Shannon.lean: from `def wiresFrom` up to
    (not including) `theorem final_gates`, namespace lines removed."""
    src = strip_comments(src)
    a = src.index("def wiresFrom")
    b = src.index("theorem final_gates")
    blk = src[a:b].rstrip()
    assert "namespace" not in blk and "import" not in blk
    return blk

checker = strip_comments(read(checker_path)).replace(LIB, AUX)
assert '"' not in checker, "Checker.lean code contains a string literal"

link = read(link_path)
link_lines = [l for l in link.splitlines() if not l.startswith("import ")]
link = strip_comments("\n".join(link_lines))
# wdt macro: delete the definition, expand the uses (before the string
# check: the macro line itself holds the only quotes in the file)
link = re.sub(r"macro \"wdt\" : tactic =>\s*\n\s*`\(tactic\| [^\n]*\)\n", "", link)
assert 'macro "wdt"' not in link
assert '"' not in link, "Link.lean code contains a string literal"
n_uses = link.count("disch := wdt")
link = link.replace("disch := wdt",
    "disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))")
assert "wdt" not in link.replace("wd_lt1", "").replace("wd_lt2", ""), "wdt remnant"
link = link.replace(" PEqualNP.MetaComplexity.Helpers", "")
link = link.replace(LIB, AUX)

shannon = shannon_block(read(shannon_path))
assert '"' not in shannon, "Shannon block contains a string literal"
shannon_txt = ("namespace " + AUX + "\n\nopen PEqualNP.CircuitLowerBounds\n\n"
               + shannon + "\n\nend " + AUX + "\n")

raw = read(raw_path)
raw_lines = [l for l in raw.splitlines() if not l.startswith("import PEqualNP.Library.LRAT")]
raw = "\n".join(raw_lines).replace(LIB, AUX)

out = ("import PEqualNP.Defs\n\n" + checker.rstrip() + "\n\n" + shannon_txt + "\n"
       + link.rstrip() + "\n\n" + raw)
open(out_path, "w").write(out)
print(f"importer ok: {len(out)} bytes, wdt uses expanded: {n_uses} -> {out_path}")
