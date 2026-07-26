# Iter-007 Recommendations

- Prover-ready: 180 passed statements. First finite-effort wave: `0005`, `0340`, `0402`, `0792`, `0882`, `0922`; each has one `sorry` and no helper-sorry debt. Preserve signatures and use the existing scalarized law/readout → `norm_num` + `linarith`/`nlinarith` pattern where applicable.
- Evidence repair, no statement churn: generate genuine current post-formalization reports for `0078`, `0135`, `0165`, `0195`, `0197`, `0206`, `0325`, `0330`, `0331`, `0384`, `0388`, `0418`, `0435`, `0441`, `0455`, `0462`, `0463`, `0465`, `0466`, `0467`, `0472`, `0478`, `0483`, `0488`, `0498`, `0513`, `0514`, `0547`, `0596`, `0611`, `0627`, `0663`, `0776`, `0786`, `0790`. A generic preflight is insufficient.
- Refresh stale reports: `0117` must document the symbolic all-distance destructive-interference iff and recorded-answer contradiction; `0629` must document the implicit Shockley/KVL equation and missing `V_in`/`R`. Do not restore their unsupported numeric conclusions.
- Import repair before re-review: add a direct `Mathlib` import to `0206` and `0472`, then verify in the Lake environment and regenerate reports.
- Blueprint repair: update `0954` target prose and `\uses{}` from the rejected undefined-`sigma` iff to the current energy/reachability result. Retain the historical Lean name only as a compatibility pin.
- Deterministic checks: rerun iter-007 blueprint doctor (iter-006 artifacts are missing), including orphan/cross-reference and physics lists; rerun marker sync; retry graph gaps with the project venv. Unmatched is currently 0.
- Infrastructure: preserve actual edit payloads in `attempts_raw.jsonl`; iter-006 has 427 blank edit records, preventing code-level attempt reconstruction. Restore run-local role/prompt files.
