# Prover result: `problem_phyx_mini_0900.lean`

## Status

Complete. All four `sorry` placeholders were replaced with sound proofs, with
no declaration signatures changed.

## Proof summary

- Proved the nanocoulomb/coulomb and centimetre/metre conversion lemmas from
  `Dimensionful`'s unit-scaling law and the corresponding Physlib unit
  definitions.
- Derived the zero sum of the two source-force components directly from force
  superposition and static equilibrium.
- Used the two `10 cm` figure gaps to establish displacements of `1/5 m` and
  `1/10 m` from `q₁` and the middle charge to `q₂`.
- Applied the signed axial Coulomb-force hypotheses, canceled the nonzero common
  factor supplied by the physical nondegeneracy assumptions, and obtained
  `q₁ = -4 q_middle`.
- Combined this with the middle `5 nC` readout to prove the target
  `chargeInNanocoulombs (setup.charge .q1) = -20`.

## Verification

- Lean LSP whole-file diagnostics: success, with no errors or warnings.
- Final theorem tactic: `goals_after: []`.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom check for
  `PhyXMiniProblems.ProblemPhyXMini0900.problem_phyx_mini_0900`: only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint note

The blueprint chapter was not edited because the task's write permissions
explicitly restrict changes to the assigned Lean file and this task-result
file.

## Redraft needed

None.
