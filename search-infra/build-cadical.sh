#!/bin/bash
# CaDiCaL build for the pequalnp LRAT pipeline. Detached, resumable by log inspection.
set -u
BASE="$HOME/workspace/pequalnp-muse"
SRC="$BASE/src/cadical"
BIN="$BASE/bin"
LOG="$BASE/search-infra/cadical-build.log"
mkdir -p "$SRC" "$BIN"
exec >>"$LOG" 2>&1
echo "[cadical] start $(date -Is)"
if [ -x "$BIN/cadical" ]; then
  echo "[cadical] already built"; "$BIN/cadical" --version; echo "[cadical] DONE"; exit 0
fi
cd "$BASE/src"
if [ ! -d cadical-repo ]; then
  git clone --depth 1 --branch rel-2.2.1 https://github.com/arminbiere/cadical.git cadical-repo || { echo "[cadical] clone FAILED"; exit 1; }
fi
cd cadical-repo
./configure >>"$LOG" 2>&1 || { echo "[cadical] configure FAILED"; exit 1; }
nice -n 10 make -j2 >>"$LOG" 2>&1 || { echo "[cadical] make FAILED"; exit 1; }
cp build/cadical "$BIN/cadical"
[ -f build/libcadical.a ] && cp build/libcadical.a "$BIN/" 2>/dev/null
"$BIN/cadical" --version
echo "[cadical] DONE $(date -Is)"
