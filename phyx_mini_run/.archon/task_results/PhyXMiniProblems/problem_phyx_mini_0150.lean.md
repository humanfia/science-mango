# Prover result: `problem_phyx_mini_0150.lean`

## Status

Lean proof complete. The assigned file already contains a sound,
signature-preserving proof of
`PhyXMiniProblems.ProblemPhyXMini0150.both_exit_angles_from_normal`, with no
remaining `sorry`. No Lean source edit was needed in Archon iteration 016.

## Proof audit

- The per-beam `forward_model` derives the symbolic emergence formula from
  the entry Snell equation, the prism angle relation, and the exit Snell
  equation.
- Positivity of the air and glass indices justifies both divisions.
- The stipulated acute physical branches justify both uses of
  `Real.arcsin_sin`.
- Bounds on the two internal angles ensure that conversion of their
  `Real.Angle` sum to real representatives introduces no quotient-angle
  wraparound.
- `MatchesShownExitLabels` transports the per-beam result to `thetaOne` and
  `thetaTwo`.
- The unused `h_readouts` premise is harmless: the theorem proves a stronger
  symbolic relation parameterized by the experiment's entry and apex angles.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0150.lean` succeeds.
  Its only diagnostic is the benign unused-variable linter warning for
  `h_readouts`.
- Source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- `lean_verify` reports only the standard foundational dependencies
  `propext`, `Classical.choice`, and `Quot.sound`, with no suspicious source
  patterns.
- No `/- USER: ... -/` hint is present in the assigned file.

## Remaining review-gate issue

The proof-review retry is blocked only by the blueprint, not by Lean. The
chapter's target `\uses{...}` list and declaration topology still mention the
removed numerical/calibration declarations
`HasSilicateFlintCalibration`, `degreeReadout`, `AnswerChoice`,
`answerAngleDegrees`, `MatchesDegreeReadoutToNearestTenth`, and
`MatchesAnswerToNearestTenth`.

The plan/review lane should synchronize the chapter with the present symbolic
contract:

- make the target depend on `PrismExperiment`, `HasStatedReadouts`,
  `SatisfiesPrismRayLaws`, `MatchesShownExitLabels`, and
  `snellPredictedEmergenceRadians`;
- remove the six stale topology entries above; and
- retain choice C (`68.1°`) only as documentary source metadata because the
  source supplies no silicate-flint dispersion calibration.

The theorem environment and proof are ready for `\leanok`. The blueprint was
not edited because prover permissions restrict blueprint chapters to
read-only and assign `\leanok` synchronization to the deterministic sync
phase.

## Redraft needed

None for the Lean theorem. The current symbolic statement is faithful and
provable; only the blueprint metadata needs synchronization.

## Environment notes

- The requested run-local `.archon/AGENTS.md` is absent. The current
  `.archon/prover-modes/physics.md` and the canonical archived `AGENTS.md`
  were used as the documented fallback.
- The optional `archon` DAG executable is not available on `PATH`.
