# Prover result: `problem_IPhO_2026_2_B_2.lean`

## Outcome

Closed the sole proof obligation without changing the declaration signature:

- `IPhO2026Problems.IPhO2026_2_B_2.problem_IPhO_2026_2_B_2`

The proof unfolds the B.1 radius relation and rewrites `sin (2 * thetaMax)`
with `Real.sin_two_mul`, obtaining
`a = R * sin(thetaMax) * (1 - cos(thetaMax))`. Positivity of the container
radius rules out `1 - cos(thetaMax) = 0`. The projected-aperture power laws
then permit cancellation of the positive irradiance, container radius, and
illuminated length, after which `nlinarith` closes the polynomial identity.

## Verification

- Lean language-server diagnostics: no errors; only unused-hypothesis linter
  warnings for physical assumptions not needed after using the supplied B.1
  and projected-power laws.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, added `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification reports only Lean/Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint status

The proof environment for
`IPhO2026Problems.IPhO2026_2_B_2.problem_IPhO_2026_2_B_2` is ready for
deterministic `\leanok` synchronization. The blueprint was not edited because
the prover role permits writes only to the assigned Lean file and this result
file.

## Redraft needed

None.
