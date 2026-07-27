# Prover result: IPhO 2026 problem 3 B.2

## Outcome

- Closed the sole placeholder in
  `IPhO2026Problems.IPhO2026_3_B_2.adiabatic_temperature_change`.
- Preserved the theorem signature and all physical hypotheses.
- Added the narrow Mathlib calculus imports for product/quotient derivatives
  and the mean-value theorem.

## Proof

The proof differentiates the equation of state on the open process interval
and combines it with the first-law/adiabatic energy balance to derive

`(λ + μ₀ K H²) T' = μ₀ K H T H'`.

It then proves that `T² / (λ + μ₀ K H²)` has zero derivative, uses Lagrange's
mean-value theorem and endpoint continuity to equate its values at `0` and
`1`, substitutes the supplied endpoint field and initial-temperature data,
and uses strict positivity to choose the positive square-root branch.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_B_2.lean` succeeds
  without diagnostics.
- Source scan finds no `sorry`, `admit`, declared `axiom`, `sorryAx`, or
  `native_decide`.
- Lean axiom verification reports only `propext`, `Classical.choice`, and
  `Quot.sound`, with no source-scan warnings.
- The blueprint theorem proof environment is ready for the deterministic
  `\leanok` synchronization phase.

## Redraft needed

None.
