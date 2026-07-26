# Prover result: `PhyXMiniProblems/problem_phyx_mini_0081.lean`

## Status

Complete. Both original `sorry` proof bodies are closed, and the frozen
declaration signatures are unchanged.

This iteration repairs the proof-review provenance failure from iteration 013:
the required nested result file now describes the current 719-line, zero-sorry
Lean source instead of the earlier autoformalization stubs.

## Proof summary

- `longerWavelengthPicometers_bounds` first proves the unit conversion
  `picometersValue length = 1000 * nanometersValue length` from the Physlib
  `LengthUnit` scales. It specializes Bragg's law to the second, first-order
  peak and rewrites the `0.94 nm` spacing to obtain
  `λ_long(pm) = 1880 * sin θ`.
- The same lemma converts the figure band
  `0.575 θₛ ≤ θ ≤ 0.6 θₛ`, with `θₛ = 2°`, into certified sine bounds on the
  physical acute-angle branch. Exact trigonometric identities, monotonicity,
  and rational square-root estimates then give
  `37 < λ_long(pm) < 40`.
- `problem_phyx_mini_0081` uses that interval to split the four displayed
  choices. It proves that `38 pm` (choice C) is strictly closer than `30 pm`,
  `35 pm`, and `25 pm`; the C-against-C branch contradicts the required
  distinctness hypothesis.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0081.lean` passed.
- `lake build` passed.
- The assigned file contains no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, `unsafe`, macro, or elaborator escape.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0081.lean` passed.
- The only compiler message is the benign linter observation that
  `h_physical` is not explicitly referenced in
  `longerWavelengthPicometers_bounds`; the proof derives its numerical result
  directly from the readouts and Bragg-law hypothesis.
- The checked source SHA-256 is
  `57a59b864b50b6d07069ccf8d484a63e9aca6b3c2612a9c56c8dfe19304ff815`.

## Blueprint synchronization

The helper lemma and target theorem are ready for `\leanok`. The blueprint was
not edited because the prover write permissions authorize changes only to the
assigned Lean file and this task-result file.

## Redraft needed

None.
