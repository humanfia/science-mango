# Prover result: `problem_phyx_mini_0386.lean`

## Outcome

- Closed all three proof obligations:
  - `displacedOceanVolume_at_requestedDraft`
  - `totalSupportedMass_at_requestedDraft`
  - `requiredConcreteMass_eq_answerB`
- No `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide` remains in the
  assigned Lean file.
- No declaration signature was changed.

## Proof summary

- The displacement lemma rewrites the prismatic displacement law with the
  supplied `3 m²` area and `10 m` draft, then proves the readout
  `3 × 10 = 30 m³`.
- The supported-mass lemma combines Archimedes' law, static equilibrium, and
  the weight law. After rewriting the calibrated density and derived volume,
  it projects the dimension-tagged equality to real readouts and cancels the
  strictly positive gravitational acceleration to obtain `29910 kg`.
- The target theorem unfolds total supported mass, rewrites the empty tank
  mass as `10000 kg`, and derives concrete mass `19910 kg`, the readout for
  answer B.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0386.lean` exits
  successfully with no diagnostics.
- Lean LSP diagnostics are empty.
- Axiom verification for
  `PhyXMiniProblems.ProblemPhyXMini0386.requiredConcreteMass_eq_answerB`
  reports only the standard trusted axioms `propext`, `Classical.choice`, and
  `Quot.sound`; the source scan reports no suspicious patterns.

## Blueprint note

The theorem is ready for `\leanok`. The blueprint chapter was not edited
because this prover role's explicit write permissions restrict changes to the
assigned Lean file and this task-result file.

## Redraft needed

None.
