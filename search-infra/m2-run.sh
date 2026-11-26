#!/bin/bash
# Milestone 2 driver: ff to upstream, rebuild LRAT modules, run the perf sweep.
set -u
export PATH="$HOME/workspace/pequalnp-muse/bin:$HOME/.elan/bin:$PATH"
BASE="$HOME/workspace/pequalnp-muse"
REPO="$BASE/pequalnp-proofs"
LOG="$BASE/search-infra/m2.log"
exec >>"$LOG" 2>&1
echo "=== m2 start $(date -Is) ==="
cd "$REPO" || exit 1
git fetch -q upstream main && git merge -q --ff-only upstream/main && git log --oneline -1 || { echo "ff FAILED"; exit 1; }
cd lean && /usr/bin/time -f "libbuild %e s" lake build PEqualNP.Library.LRAT.Link PEqualNP.Library.LRAT.Checker 2>&1 | tail -3
cd "$BASE"
nice -n 10 python3 search-infra/m2-perf.py
echo "=== m2 end $(date -Is) ==="
