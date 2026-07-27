# Prover result: IPhO 2026 problem 4 C.7

## Status

Complete. The sole `sorry` in
`acrylicConductivity_from_radial_fourier` was replaced by a sound proof.

The endpoint step defines the logarithmic radial-temperature model,
establishes that it and the measured profile have the same derivative and
initial value on the wall interval, applies `eq_of_has_deriv_right_eq`, and
then rewrites the inner and outer boundary temperatures. The remaining
conductivity formula follows by the existing algebraic argument.

Added the standard
`Mathlib.Analysis.SpecialFunctions.Log.Deriv` import, which supplies both
`Real.hasDerivAt_log` and the interval derivative-uniqueness result required
by this proof. No declaration signature or physical hypothesis was changed.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_C_7.lean`: passed
  (only the pre-existing unused-`previousPart` linter warning).
- `lake build`: passed.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom verification for
  `IPhO2026Problems.IPhO2026_4_C_7.acrylicConductivity_from_radial_fourier`:
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

`IPhO2026Problems.IPhO2026_4_C_7.acrylicConductivity_from_radial_fourier`
is ready for the deterministic `\leanok` synchronization.

## Redraft needed

None.
