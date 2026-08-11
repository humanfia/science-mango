# IChO 2026 K3 formalizations

This Lake project contains Lean formalizations for 32 selected theory-ready
subquestions from the IChO 2026 theory papers T1--T9. The practical papers
P1--P3 are outside this release's scope.

The work was rerun from the `chemistry` branch with `kimi-k3[1m]` through a
Claude Code harness. Prior GPT-produced problem proof files were not imported.
This was not strict per-target filesystem isolation: a small number of K3
workers consulted sibling K3 files from the same run for formatting patterns.

All 32 selected subquestions pass the current statement and proof checks,
direct Lean preflight, and the default Lake build. This means 32/32 within the
published target set; it is not a claim of a full score on the complete IChO
exam. Detailed validation results and the T8-A6 source discrepancy are recorded
in [RESULTS.md](RESULTS.md).

## Build

```bash
lake exe cache get
lake build
```

The selected target list is `references/icho_2026_theory_ready.jsonl`.

- [Source code](https://github.com/humanfia/science-mango/tree/chemistry-K3/icho_2026_run)
- [Dataset](https://huggingface.co/datasets/humanfia-lab/icho-2026-lean4-formalizations)
