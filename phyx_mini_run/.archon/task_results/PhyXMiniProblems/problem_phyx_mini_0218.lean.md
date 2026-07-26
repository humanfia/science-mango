# Prover result: `problem_phyx_mini_0218.lean`

## Status

All three assigned declarations are proved with their signatures unchanged:

- `fingeredVibratingLength_ratio`
- `firstFretPosition_exactFormula`
- `firstFretPosition_matches_recordedAnswerD`

No `sorry` remains.

## Proof summary

- The stretched-string laws for the open and fingered configurations are
  rewritten using unchanged tension and linear mass density. Positivity of
  those quantities makes their common square-root factor nonzero, so the
  semitone frequency relation yields the inverse vibrating-length ratio.
- The figure's segment-partition equation and the `75 cm` readout then give
  the exact first-fret position
  `75 * (1 - 1 / 2^(1/12))`.
- For the displayed answer, the proof establishes
  `1500/1417 < 2^(1/12) < 300/283` by comparing twelfth powers. The resulting
  reciprocal bounds prove that the exact position is within `0.05 cm` of
  `4.2 cm`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0218.lean`: passed.
- `lake build`: passed.
- Lean LSP diagnostics: no errors or warnings.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Declaration axiom check reports only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The proof environments for `fingeredVibratingLength_ratio`,
`firstFretPosition_exactFormula`, and
`firstFretPosition_matches_recordedAnswerD` are ready for `\leanok`.
The blueprint was not edited because it is read-only for the prover role.

## Redraft needed

None.
