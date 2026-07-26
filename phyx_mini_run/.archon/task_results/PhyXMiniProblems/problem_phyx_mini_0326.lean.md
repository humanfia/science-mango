# Prover result: `problem_phyx_mini_0326.lean`

## Completed declarations

- `surfaceWaveIntensityAtStation_formula`: proved by establishing positivity of
  the cylindrical wavefront area, then applying the local lossless-intensity,
  power, energy-partition, impact-energy, and cylindrical-geometry laws in
  sequence. Ring normalization closes the resulting division identity.
- `problem_phyx_mini_0326`: proved the mass-dependent kilowatt formula, derived
  the Physlib conversion from the `200 km` readout to `200 * 1000 m`, propagated
  the measured mass interval monotonically through the positive intensity
  formula, and used `Real.pi_gt_three` to show the entire modeled interval lies
  below the rounding window for the recorded `58 kW/m²` answer.

The theorem signatures and all physical hypotheses were left unchanged. There
are no remaining `sorry` placeholders and no redraft is needed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0326.lean` succeeds with no
  errors or warnings.
- `lean_verify` reports no source-scan warnings for either completed
  declaration; their only dependencies are the standard `propext`,
  `Classical.choice`, and `Quot.sound` axioms.
- A scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide` in
  the assigned file.
- `.archon/AGENTS.md` is absent in this checkout; the prompt-supplied role,
  `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, the source report,
  and the assigned blueprint chapter were followed.
- The assigned file contains no `/- USER: ... -/` comments.

## Blueprint synchronization

The blueprint environments were not marked `\leanok` because this prover lane's
explicit write permissions allow edits only to the assigned Lean file and this
task-result file. The synchronization/plan agent should mark
`surfaceWaveIntensityAtStation_formula` and `problem_phyx_mini_0326` as
`\leanok`.
