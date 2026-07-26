# Prover result: `problem_phyx_mini_0967.lean`

## Outcome

- `rotatingCylinderIdealInteriorFieldMagnitudeFormula`,
  `idealMagneticDipoleTorqueMagnitudeFormula`, and the target theorem
  `problem_phyx_mini_0967` are fully proved.
- The target theorem evaluates the ideal torque to displayed answer B and
  proves the actual finite-apparatus error bound directly from the magnetic
  dipole torque law, the reverse triangle inequality, and the stored torque
  remainder contract.
- `finiteApparatusTorqueMagnitudeErrorBound` retains one focused `sorry`.
  Its proof derives the full vector-norm estimate and reduces the remaining
  gap to the unavailable equality between the independently stored ideal
  torque magnitude and the norm of the ideal torque vector.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0967.lean` succeeds.
- The only proof warning is the expected `sorry` warning on
  `finiteApparatusTorqueMagnitudeErrorBound`.
- Axiom checks for the two completed lemmas and `problem_phyx_mini_0967`
  report only standard Lean/Mathlib axioms (`propext`, `Classical.choice`,
  and `Quot.sound`), with no `sorryAx`.
- The incomplete helper alone reports `sorryAx`; the target theorem does not
  depend on it.

## Redraft needed

- Original problem id: `phyx_mini_0967`
- Source report: `reports/phyx_mini/problem_phyx_mini_0967.source.json`
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0967.finiteApparatusTorqueMagnitudeErrorBound`
- Why the statement is not provable: its sole law hypothesis,
  `SatisfiesFiniteApparatusTorqueApproximation setup`, identifies the actual
  scalar torque magnitude with the norm of the actual torque vector,
  decomposes the actual vector as ideal vector plus remainder, and bounds
  that remainder. It does not identify
  `setup.idealMagneticTorqueMagnitude` with the norm of
  `setup.idealMagneticTorqueVector`. Those are independent fields of
  `RotatingCylinderDiskSetup`, so the desired scalar inequality does not
  follow. For example, the approximation fields can consistently have zero
  actual, ideal-vector, remainder, and error-bound readouts while the
  independent ideal scalar magnitude has a positive readout.
- Smallest faithful statement change: add
  `(torqueLaw : SatisfiesMagneticDipoleTorqueLaw setup)` as a hypothesis.
  Then `torqueLaw.idealTorqueMagnitudeIsVectorNorm` supplies the missing
  rewrite and the completed vector-norm estimate closes the theorem.

## Blueprint status

- Proof-level `\leanok` is justified for
  `rotatingCylinderIdealInteriorFieldMagnitudeFormula`,
  `idealMagneticDipoleTorqueMagnitudeFormula`, and
  `problem_phyx_mini_0967`.
- It is not justified for `finiteApparatusTorqueMagnitudeErrorBound`.
- The blueprint was not edited because the active prover write permissions
  allow changes only to the assigned Lean file and this task-result file.
