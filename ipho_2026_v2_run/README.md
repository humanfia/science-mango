# IPhO 2026 Lean formalizations and solutions

This directory joins the 28 natural-language formalization-ready records with
their Lean artifacts.

## Dataset files

- `ipho_2026_formalized.jsonl`: all 28 selected rows. Each row embeds the
  original record, formal blueprint, full Lean module, latest solution report,
  and Review status.
- `ipho_2026_lean_verified.jsonl`: the 22 theory rows that passed strict
  semantic Review and proof Review and contain zero `sorry`.
- `IPhO2026Problems/`: complete Lean modules.
- `blueprint/`: declaration-level problem specifications and dependencies.
- `reports/solutions/`: per-target proof/formalization reports.
- `reports/final/`: gate snapshots, comparison data, and run summaries.

## Status

All 22 theory targets are verified. Six experimental E1 targets were
user-skipped and retain partial formalizations; their rows use
`lean_status = "skipped_experimental"` and `lean_verified = false`.

## Build

```bash
lake exe cache get
lake build
```
