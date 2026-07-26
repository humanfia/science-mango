# Iter-012 Recommendations

## Blockers first

- Do not reassign any of the 32 iter-011 objectives; all are directly elaborated, sorry-free, grounded, and semantically certified.
- Route the two live doctor findings through an authorized structural Lean-writing lane:
  - `PhyXMiniProblems/problem_phyx_mini_0206.lean` — add a real Mathlib import and verify in the Lake/Mathlib environment.
  - `PhyXMiniProblems/problem_phyx_mini_0472.lean` — add a real Mathlib import and verify in the Lake/Mathlib environment.
- Keep the global project verdict blocked until both doctor entries disappear. Their exact reason is that a physics target without Mathlib cannot be accepted from a standalone smoke check.

## Next proof wave

- Select new targets only from the formalization-review-passed, grounded frontier. The current batch reduces the reviewed queue to approximately 920 sorry-bearing files.
- Preserve source-honest exceptions: `0380` supports only the symbolic weighted-density formula; do not inject uncited granite, sand, or water densities to recover a numerical answer.
- Preserve corrected dataset conflicts: `0016` is answer B/about `27.5°`, and `0346` is answer A/about `28°C`.

## Reusable proof patterns

- For acute optical inversions, derive sine bounds first, prove the angle lies in the principal interval, and only then use sine monotonicity or `arcsin`/`arctan` inversion (`0000`, `0001`, `0007`, `0009`, `0016`, `0017`, `0021`).
- When exact library pi bounds are unavailable, bootstrap the needed rational interval locally from `Real.sin_bound` and coarse facts such as `Real.pi_le_four` (`0000`, `0013`, `0303`).
- For extrema and least-value statements, supply both the boundary witness and the universal comparison; an endpoint equation alone is insufficient (`0009`, `0010`, `0012`, `0015`, `0021`, `0025`).
- Keep dimensional quantities and geometric vectors intact through the physics argument, scalarizing only at named SI/readout boundaries (`0002`, `0003`, `0012`, `0022`, `0023`, `0026`, `0027`).
- In repair retries, normalize the exact representation before changing angle forms, remove progress-demanding tactics after closure, and make positivity/nonzeroness explicit before cancellation (`0061`, `0346`, `0380`, `0458`).

## Evidence and controls

- Continue using per-target grounding logs with actual queries/candidates, grounded names, local abstractions, and explicit gaps; a successful compile is not a semantic review.
- Preserve the current iter-011 sync attribution: it checked exactly the 32 objectives and made no marker changes.
- Linter-only unused-hypothesis warnings may be cleaned later, but do not delete source/figure parameters merely to silence warnings; first decide whether they are required for parameter capture or branch documentation.
