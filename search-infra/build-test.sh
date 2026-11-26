#!/bin/bash
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/workspace/pequalnp-muse/pequalnp-proofs/lean" || exit 1
exec >>"$HOME/workspace/pequalnp-muse/search-infra/build-test.log" 2>&1
echo "=== build test start $(date -Is) ==="
time lake build PEqualNP.Outside.L_import_test
echo "=== build test exit $? $(date -Is) ==="
rm -f PEqualNP/Outside/L_import_test.lean
