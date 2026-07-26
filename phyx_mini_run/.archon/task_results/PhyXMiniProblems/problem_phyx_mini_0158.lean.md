# Prover result: `problem_phyx_mini_0158.lean`

## Status

Lean proof complete. The assigned file already contained sound,
signature-preserving proofs of
`apparentDepth_eq_trueDepth_mul_indexRatio` and
`problem_phyx_mini_0158`, with no remaining `sorry`, when Archon iteration
016 began. No Lean source edit was needed.

## Proof audit

- Positivity from `HasPhysicalOpticalParameters` makes the glass refractive
  index and refracted slope nonzero.
- `apparentDepth_eq_trueDepth_mul_indexRatio` combines the two common-ray-height
  equations from `HasParaxialRayGeometry`, substitutes the first-order Snell
  relation, and cancels those nonzero factors to derive
  `s' = s * n₂ / n₁`.
- `problem_phyx_mini_0158` rewrites the generic result with the figure
  identifications `s' = apparentDepthSeenBy fish`, `s = bubbleDepth`, `n₁ =
  glass`, and `n₂ = surroundingWater`, then uses the stated midpoint of the
  `5 cm` porthole to obtain `(5/2) * n_water / n_glass`.
- The theorem correctly remains symbolic: neither the source text nor the
  primary figure supplies numerical glass or water refractive indices.

## Verification

- Lean LSP diagnostics are empty.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0158.lean` exits with code
  0 and no output.
- The project-wide default `lake build` completes successfully.
- Source scans find no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, unsafe declaration, or metaprogramming escape.
- `lean_verify` reports only the standard foundational dependencies
  `propext`, `Classical.choice`, and `Quot.sound`, with no suspicious source
  patterns, for both proved declarations.

## Remaining review-gate issue

The iteration-015 proof review marked this file `partial` only because the
blueprint target and topology still list removed numerical calibration,
rounding, and closest-answer dependencies. The current Lean theorem and proof
consistently give the strongest source-supported symbolic answer and treat
recorded choice B as metadata.

An authorized blueprint-editing lane should remove
`HasStandardMaterialReadouts`, `IsNearestTenthCentimeterReadout`, and
`IsClosestDepthAnswer` from the target dependencies/topology and retain
`recordedAnswerChoice` as metadata. Both the supporting lemma and target
theorem are ready for `\leanok`; the blueprint was not edited because prover
permissions make it read-only and assign marker updates to deterministic
synchronization.

## Redraft needed

None for the Lean theorem. Its current symbolic statement is faithful and
provable; only blueprint metadata needs synchronization.

## Environment notes

- The file-specific user comment only records that the assigned Lean file did
  not exist when autoformalization began; it gives no proof-specific hint.
- The requested run-local `.archon/AGENTS.md` is absent. The current
  `.archon/prover-modes/physics.md` and canonical archived `AGENTS.md` were
  used as the documented fallback.
