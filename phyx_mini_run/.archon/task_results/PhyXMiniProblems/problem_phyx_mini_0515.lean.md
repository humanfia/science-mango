# Prover result: `problem_phyx_mini_0515.lean`

## Outcome

Complete. Both assigned `sorry` placeholders were replaced with sound proofs
without changing any declaration signature.

- `workFunction_eq_planckAction_mul_thresholdFrequency` specializes Einstein's
  photoelectric equation at the threshold frequency, rewrites the plotted
  stopping potential to the graph's zero vertical intercept, and derives
  `φ = h f₀` by linear arithmetic.
- `photoelectric_workFunction_matches_choiceD` combines that exact relation
  with the graph calibration `f₀ = (5/4)·10^15 Hz`, the exact Planck-constant
  readout, and Physlib's definition
  `1 eV = 1.602176634·10⁻¹⁹ J`. Exact rational normalization proves the
  `0.4 eV` error bound and checks choice D against each of A, B, C, and D.

The frozen `hScenario` and `hPhysical` inputs are not needed after the stronger
graph, reference-data, and governing-law hypotheses determine the conclusion;
Lean therefore emits only the corresponding unused-variable linter warnings.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0515.lean` succeeds.
- `lake build` succeeds (`4 jobs`).
- The assigned file contains no `sorry`, `admit`, `sorryAx`, `native_decide`,
  or local `axiom` declaration.
- Axiom inspection of both proved declarations reports only the standard
  imported axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` succeeds.

## Blueprint status

Both the supporting lemma and target theorem are ready for deterministic
`\leanok` synchronization. The blueprint chapter was not edited because prover
write permissions reserve marker updates for the synchronization/review phase.

## Redraft needed

None.
