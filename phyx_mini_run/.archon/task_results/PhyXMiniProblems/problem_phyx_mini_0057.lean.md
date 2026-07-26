# Prover result: `PhyXMiniProblems/problem_phyx_mini_0057.lean`

## Outcome

- Closed `surfaceCurvatureReadouts` by unpacking the two surface-profile
  readouts and reducing the curvature definition.
- Closed `reciprocalFocalLength_eq_twenty_one_over_one_sixty` by substituting
  the `8 mm` object distance and `160 mm` image distance into the thin-lens
  equation.
- Closed `curvedSurfaceRadius_eq_eighty_over_twenty_one` by combining the
  thin-lens result with the lensmaker equation, the glass/air refractive
  indices, the signed surface curvatures, and radius positivity. Clearing the
  nonzero radius denominator reduces the equation to `R = 80 / 21`.
- Closed `problem_phyx_mini_0057`; exact rational normalization proves that
  `80 / 21 mm` is within `0.05 mm` of answer choice C's `3.8 mm`.
- All declaration signatures and physical-model definitions were preserved.
- No redraft is needed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0057.lean`: passed with
  no output.
- Lean LSP diagnostics: empty.
- Source/axiom verification reports no suspicious proof constructs. The final
  theorem depends only on the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- Remaining `sorry` count: zero.

## Blueprint status

The three helper lemmas and target theorem are proof-complete and ready for
deterministic `\leanok` synchronization. The blueprint was not edited because
prover-role permissions make it read-only.

## Redraft needed

None.

## Project-instruction note

The requested run-local `.archon/AGENTS.md` is absent. As documented in
`.archon/PROGRESS.md`, the canonical archived `AGENTS.md` and the run-local
`.archon/prover-modes/physics.md` supplied the applicable prover instructions.
