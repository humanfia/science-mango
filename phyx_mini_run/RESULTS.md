# PhyX-mini Full-Run Results

This directory preserves the reviewable outputs from the local PhyX-mini
experiment snapshot completed on 2026-07-26.

## Result summary

- Dataset coverage: 1,000 / 1,000 targets (`phyx_mini_0000` through
  `phyx_mini_0999`).
- Generated outputs: 1,000 Lean files and 1,000 source-report JSON files.
- Formalization Review: 963 passed, 37 review-exhausted.
- Proof Review: 933 solved and 24 proof-review-exhausted among 957 tracked
  targets.
- Six certified targets predate proof-gate tracking.
- Overall certified result: 939 / 1,000 targets (93.9%).
- Remaining proof placeholders: 93 across 46 Lean files.
- The final wrapper stopped at its configured 100-iteration limit after the
  deterministic planner found no further gate-eligible objectives.

This is a full-coverage experiment, not a 100% successful proof run. The
remaining 61 targets consist of 37 formalization-review-exhausted targets and
24 proof-review-exhausted targets. Fifteen of the latter have no textual
placeholder but did not pass semantic/elaboration review.

## Included outputs

- `PhyXMiniProblems/`: all 1,000 generated Lean targets.
- `reports/phyx_mini/`: all 1,000 source-report JSON files.
- `blueprint/`: the generated Lean blueprint.
- `.archon/physics-formalize/`: the full 1,000-row preparation manifest and
  summary.
- `.archon/formalization-review-gate.json`: per-target formalization verdicts.
- `.archon/proof-review-gate.json`: per-target proof verdicts.
- `.archon/task_results/`: 1,406 task result records.
- `.archon/proof-journal/`: 328 proof-review journal files.
- `.archon/iter/`: compact per-iteration plan/review summaries.
- `run_logs/`: top-level orchestration logs, including the final 100-iteration
  proof run.
- `result-summary.json`: machine-readable aggregate counts.

## Deliberately excluded

The following local-only material is not committed:

- `.lake/` (8.2 GB dependency/build cache).
- `.archon/logs/` (2.6 GB raw agent traces, including individual files over
  GitHub's 100 MB limit). Compact task results, proof journals, iteration
  summaries, and wrapper logs are included instead.
- `.git/`, `.leandag/`, process IDs, and other runtime caches.
- `.archon/.env`, SSH keys, API credentials, and local MCP settings.
- Input image copies, the source parquet file, and superseded local archives;
  these are inputs or duplicate snapshots rather than experiment outputs.

## Provenance note

The `physics` branch is rooted at science-mango commit
`7915988e1cc5a2d8fa408d1d77dddb5df8e38d3a`. The run artifacts themselves do
not record an Archon source commit SHA, so this placement preserves the local
result snapshot but does not independently prove that every stage was executed
from that exact source revision.
