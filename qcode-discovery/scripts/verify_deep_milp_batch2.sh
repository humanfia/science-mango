#!/bin/bash
# Deep MILP batch 2: re-run (12,6) with 7200s timeout + (15,6) and (30,6)
# Run after batch 1 completes.
#
# Usage: nohup bash scripts/verify_deep_milp_batch2.sh > results/verify_deep_milp_batch2.log 2>&1 &

set -e

echo "=== Deep MILP Batch 2 ==="
echo "Started: $(date)"
echo ""

# First: merge the split batch 1 output files (rename caused split)
echo "--- Merging batch 1 output files ---"
if [ -f results/campaign7g_deep_milp.jsonl ] && [ -f results/campaign7_deep_milp.jsonl ]; then
    # Append old-name file entries to the canonical file, avoiding duplicates
    python3 -c "
import json

existing = set()
with open('results/campaign7_deep_milp.jsonl') as f:
    for line in f:
        c = json.loads(line.strip())
        key = (str(c['A_terms']), str(c['B_terms']), str(c['C_terms']), str(c['D_terms']), c['ell'], c['m'])
        existing.add(key)

added = 0
with open('results/campaign7g_deep_milp.jsonl') as f:
    with open('results/campaign7_deep_milp.jsonl', 'a') as out:
        for line in f:
            c = json.loads(line.strip())
            key = (str(c['A_terms']), str(c['B_terms']), str(c['C_terms']), str(c['D_terms']), c['ell'], c['m'])
            if key not in existing:
                out.write(line)
                existing.add(key)
                added += 1
print(f'Merged: {added} new entries from campaign7g file')
"
    echo "Merged. Removing old file."
    rm results/campaign7g_deep_milp.jsonl
fi
echo ""

# Phase 1: Re-run (12,6) with 7200s timeout for codes that stayed partial
echo "--- Phase 1: (12,6) re-run with 7200s timeout ---"
uv run python scripts/verify_deep_milp.py \
    --workers 60 --timeout 7200 \
    --lattices 12,6 \
    --min-fom 5.0 \
    --rerun-partial \
    --output results/campaign7_deep_milp.jsonl

echo ""
echo "--- (15,6) and (30,6) running on remote server ---"
echo "--- See scripts/verify_deep_milp_remote.sh ---"
echo ""
echo "=== Batch 2 complete: $(date) ==="
