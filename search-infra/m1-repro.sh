#!/bin/bash
# Milestone 1: reproduce L_meta_2229 (n=5, s=4, edges 03,04,12,13,14) via mkrow.py
# and get ACCEPTED from the local official checker (tools/check-lean.mjs).
# Staged and checkpointed: a stage is skipped when its .done marker exists.
set -u
export PATH="$HOME/workspace/pequalnp-muse/bin:$HOME/.elan/bin:$PATH"
BASE="$HOME/workspace/pequalnp-muse"
REPO="$BASE/pequalnp-proofs"
WORK="$BASE/search-infra/work"
LOG="$BASE/search-infra/m1.log"
mkdir -p "$WORK/sub"
exec >>"$LOG" 2>&1
echo "=== m1 start $(date -Is) ==="

# --- Stage A: build the project library modules the proof rests on ---
if [ ! -f "$WORK/A.done" ]; then
  echo "[A] lake build Link + Checker ..."
  (cd "$REPO/lean" && time lake build PEqualNP.Library.LRAT.Link PEqualNP.Library.LRAT.Checker) || { echo "[A] FAILED"; exit 1; }
  touch "$WORK/A.done"; echo "[A] done $(date -Is)"
fi

# --- Stage B: regenerate with the real namespace and shape it for submission ---
if [ ! -f "$WORK/B.done" ]; then
  echo "[B] mkrow + postprocess ..."
  cd "$REPO/notes/data/lrat-link" || exit 1
  python3 mkrow.py 5 4 03,04,12,13,14 "$WORK/sub/raw.lean" "PEqualNP.Outside.L_meta_2229" --work "$WORK/cache" || { echo "[B] mkrow FAILED"; exit 1; }
  python3 - "$WORK/sub/raw.lean" "$WORK/sub/L_meta_2229.lean" <<'PY' || { echo "[B] postprocess FAILED"; exit 1; }
import re, sys
src = open(sys.argv[1]).read()
# strip all comments (block, doc, line) -- the plain-file rules are strictest about comments
src = re.sub(r'/\-!.*?\-\/', '', src, flags=re.S)
src = re.sub(r'/\-\-.*?\-\/', '', src, flags=re.S)
src = re.sub(r'/\-(?![-!]).*?\-\/', '', src, flags=re.S)
src = re.sub(r'(?m)^\s*--.*$', '', src)
# plain set_option commands are not allowed; re-attach them as `in` options on the heavy theorem
src = src.replace('set_option maxRecDepth 1000000\n', '')
src = src.replace('set_option maxHeartbeats 0\n', '')
src = src.replace('theorem unsat',
  'set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 0 in\ntheorem unsat', 1)
# final theorem: exactly the posted statement of L_meta_2229 (with its ReadsBack hypothesis)
final = '''
theorem PEqualNP.Outside.L_meta_2229 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) → 5 ≤ C.size := by
  intro C hC _ hev
  exact PEqualNP.Outside.L_meta_2229.lower C hC hev
'''
src = src.rstrip() + '\n' + final
open(sys.argv[2], 'w').write(src)
print('postprocess ok')
PY
  # statement file: the posted statement as a bare term (CheckLemma parses it as a term)
  cat > "$WORK/sub/statement.lean" <<'EOF'
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) → 5 ≤ C.size
EOF
  touch "$WORK/B.done"; echo "[B] done $(date -Is)"
fi

# --- Stage C: place into the tree, run the official checker, restore the original ---
TARGET="$REPO/lean/PEqualNP/Outside/L_meta_2229.lean"
cp "$WORK/sub/L_meta_2229.lean" "$TARGET"
echo "[C] check-lean.mjs ..."
(cd "$REPO" && time node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2229.lean "$WORK/sub/statement.lean")
rc=$?
echo "[C] checker exit code: $rc"
git -C "$REPO" checkout -- lean/PEqualNP/Outside/L_meta_2229.lean
echo "[C] original file restored; git status:"; git -C "$REPO" status --porcelain | head
echo "=== m1 end rc=$rc $(date -Is) ==="
