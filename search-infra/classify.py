#!/usr/bin/env python3
"""Step classifier for pequalnp lower-bound steps (milestone 3, first cut).

Input: a statement text (from `.pnp/<id>.json` gap.statement, or extracted
from a merged Outside file's final theorem). Output: A / B / C + reasons.

A: plain edge-function lower bound the LRAT pipeline proves as-is
   (side conditions the pipeline's `lower` already implies, e.g. a
   ReadsBack hypothesis, are noted but stay A).
B: lower bound with side conditions that need a bridging lemma
   (fixed first gate, read-count limits, derived inputs, promise).
C: anything else (SAT-side encoding statements, upper bounds / existence,
   other conclusion shapes).
"""
import re, sys

def classify(stmt: str):
    s = " ".join(stmt.split())
    reasons = []
    cls = None
    # circuit class
    if "Monotone2" in s: reasons.append("class=Monotone2")
    if "FanInTwo" in s: reasons.append("class=FanInTwo")
    # conclusion shape: the part after the last arrow at top level is hard to
    # parse textually; use characteristic tails instead.
    exact = re.search(r"RepSizeAtMost\s+(.+?)\s+(\d+)\s*∧\s*¬\s*(?:\S+\.)?RepSizeAtMost\s+(.+?)\s+(\d+)\s*$", s)
    if exact:
        return "B", reasons + [f"conclusion=exact size (RepSizeAtMost {exact.group(2)} and not "
                               f"{exact.group(4)}): lower half is pipeline-provable, upper half "
                               "needs an explicit circuit"]
    # promise-mask lower bound: the rep_lower_mask shape
    #   ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) s
    mask = re.search(r"¬\s*\(?\s*(?:\S+\.)?RepSizeAtMost\s*\(fun\s+(.*?)\s*=>\s*"
                     r"(?:\(?\s*(\d+)\s*:\s*ℕ\s*\)?\.testBit|(\d+)\.testBit|Nat\.testBit\s+(\d+))"
                     r"\s*\(\s*(\d+)\s*\*\s*\w+(?:\.val)?\s*\+\s*\w+(?:\.val)?\s*\)\)\s*(\d+)\s*\)?\s*$", s)
    if mask:
        fins = re.findall(r"Fin\s+(\d+)", mask.group(1))
        if len(fins) >= 1:
            # shared binder `fun u v : Fin 4` gives one Fin for both sides
            m_lit = mask.group(2) or mask.group(3) or mask.group(4)
            n_, m_ = int(fins[0]), int(fins[1]) if len(fins) >= 2 else int(fins[0])
            M_, s_ = int(m_lit), int(mask.group(6))
            return "B", reasons + [f"subtype=promise-mask n={n_} m={m_} M={M_} s={s_} "
                                   "(mkpromiserow-ready: genpromise + rep_lower_mask)"]
    if re.search(r"¬\s*\(?\s*(?:\S+\.)?RepSizeAtMost\b", s):
        return "B", reasons + ["subtype=promise-other (RepSizeAtMost lower bound, "
                               "function not a testBit mask lambda)"]
    lower = re.search(r"(\d+)\s*≤\s*\S+\.size\b", s)
    upper = re.search(r"\.size\s*≤\s*(\d+)", s)
    # link-specialized: a universal statement whose conclusion is
    # FormulaSat (enc N S g rows) under Monotone2 / size hypotheses
    # (the L_meta_3644 shape; no SAT needed, Link's proof specialized)
    if "FormulaSat" in s and "Monotone2" in s:
        encm = (re.search(r"\benc\s*\(\s*(\d+)\s*:\s*ℕ\s*\)\s*\(\s*(\d+)\s*:\s*ℕ\s*\)", s)
                or re.search(r"\benc\s+(\d+)\s+(\d+)\b", s))
        if encm:
            return "L", reasons + [f"subtype=link-specialized n={encm.group(1)} s={encm.group(2)} "
                                   "(Link.valid_ofCirc/exists_nf/enc_sat specialized; no SAT)"]
    if "FormulaSat" in s and "enc" in s:
        return "C", reasons + ["conclusion=FormulaSat(enc ...) (SAT-side)"]
    if lower:
        reasons.append(f"conclusion=lower-bound {lower.group(1)} <= size")
        cls = "A"
    elif upper:
        return "C", reasons + ["conclusion=size upper bound (existence side)"]
    else:
        return "C", reasons + ["no size lower-bound conclusion found"]
    # edge function as an explicit lambda over && / ||
    if re.search(r"fun z.*=>.*&&.*\|\|", s) or re.search(r"fun z.*=>.*&&", s):
        reasons.append("function=edge-lambda")
    else:
        reasons.append("function=NOT a plain edge lambda")
        cls = "B" if cls == "A" else cls
    # side conditions
    if "ReadsBack" in s:
        reasons.append("side=ReadsBack (droppable: pipeline proves without it)")
    if re.search(r"first|First", s):
        reasons.append("side=first-gate condition -> bridging lemma needed"); cls = "B"
    if re.search(r"reads|Reads(?!Back)|readCount|countReads", s):
        reasons.append("side=read-count condition -> bridging lemma needed"); cls = "B"
    if re.search(r"promise|Promise", s):
        reasons.append("side=promise -> bridging lemma needed"); cls = "B"
    return cls, reasons

def extract_statement(path: str):
    src = open(path).read()
    m = re.search(r"theorem\s+PEqualNP\.Outside\.(\S+)\s*:\s*(.*?)\s*:=", src, re.S)
    if not m: return None, None
    return m.group(1), m.group(2)

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--scan":
        import glob, collections
        dist = collections.Counter(); examples = {}
        for p in sorted(glob.glob(sys.argv[2]))[: int(sys.argv[3]) if len(sys.argv) > 3 else 10**9]:
            name, stmt = extract_statement(p)
            if stmt is None: dist["NOEXTRACT"] += 1; continue
            c, _ = classify(stmt); dist[c] += 1
            examples.setdefault(c, name)
        print(dist); print(examples)
    else:
        stmt = open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()
        c, r = classify(stmt)
        print(c, "|", "; ".join(r))
