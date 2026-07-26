# Prover result: `problem_phyx_mini_0077.lean`

## Status

Complete. All three `sorry` placeholders were replaced by sound proofs without
changing any declaration signature.

## Proof summary

- `finalImageDistanceInCentimeters_eq_thirty`: specializes the paraxial
  imaging law to initial slopes `0` and `1`, unfolds the complete round-trip
  ray transfer, rewrites the independent figure readouts, and solves the two
  resulting linear equations to obtain the `30 cm` image-plane distance.
- `signedFinalImageHeightInCentimeters_eq`: uses the derived distance and the
  zero-slope ray equation to compute the common signed transverse height as
  `-8/3 cm`.
- `problem_phyx_mini_0077`: combines that negative signed height with the
  strictly positive physical height readout. The upright branch is
  contradictory, while the inverted branch gives exact magnitude `8/3 cm`;
  direct rational arithmetic then verifies that it lies within answer C's
  `2.7 ± 0.05 cm` display tolerance.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0077.lean` succeeded.
- `lake build` succeeded.
- Lean LSP diagnostics reported no errors. The sole warning is that the frozen
  `h_physical` parameter of `finalImageDistanceInCentimeters_eq_thirty` is not
  needed: the figure data and two imaging-law specializations already determine
  the distance.
- Source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- Axiom verification for all three completed declarations reported only the
  standard imported axioms `propext`, `Classical.choice`, and `Quot.sound`,
  with no suspicious-source warnings.

## Blueprint readiness

The proof blocks for `finalImageDistanceInCentimeters_eq_thirty`,
`signedFinalImageHeightInCentimeters_eq`, and `problem_phyx_mini_0077` are
proof-closed and ready for `\leanok`. The blueprint was not edited because the
active prover permissions reserve marker synchronization for the loop.

## Redraft needed

None.
