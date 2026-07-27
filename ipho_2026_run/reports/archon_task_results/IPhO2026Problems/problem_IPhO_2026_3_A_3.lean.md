# Prover result: `problem_IPhO_2026_3_A_3.lean`

## Outcome

Closed the sole proof obligation without changing the declaration signature:

- `materialWork_eq_mu0_mul_volume_mul_H_mul_dM`

The proof first solves the source-work partition for the material work. It then
substitutes the A.2 work formulas for the actual and vacuum-core systems, uses
the actual and vacuum incremental constitutive laws, and normalizes the
resulting polynomial identity. The common `μ₀ V H dH` contribution cancels,
leaving `μ₀ V H dM`.

## Verification

- Lean language-server diagnostics: no errors or warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, added `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification reports only Lean/Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint status

The theorem environment for
`IPhO2026Problems.IPhO2026_3_A_3.materialWork_eq_mu0_mul_volume_mul_H_mul_dM`
is ready for deterministic `\leanok` synchronization. The blueprint was not
edited because the prover role permits writes only to the assigned Lean file
and this result file.

## Redraft needed

None.
