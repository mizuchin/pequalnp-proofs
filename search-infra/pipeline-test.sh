#!/bin/bash
cd "$HOME/workspace/pequalnp-muse" || exit 1
exec >>"$HOME/workspace/pequalnp-muse/search-infra/pipeline-test.log" 2>&1
echo "=== pipeline test start $(date -Is) ==="
python3 search-infra/pipeline.py L_meta_2229 search-infra/work/stmt2229.txt
echo "=== pipeline test exit $? $(date -Is) ==="
