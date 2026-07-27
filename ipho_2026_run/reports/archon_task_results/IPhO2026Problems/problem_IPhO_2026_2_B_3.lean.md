# Prover result: `problem_IPhO_2026_2_B_3.lean`

## Outcome

Closed the sole proof obligation without changing the declaration signature:

- `IPhO2026Problems.IPhO2026_2_B_3.radius_for_fivefold_power`

The fivefold-power condition and the positive baseline power reduce the B.2
ratio law to `1 / (1 - cos thetaMax) = 5`, hence
`cos thetaMax = 4 / 5`. The stated angle range selects the nonnegative sine,
so the Pythagorean identity gives `sin thetaMax = 3 / 5`. Substitution into
the B.1 geometry law, using the double-angle formula, gives the container
radius `3 / 25` metres. Finally, the `Dimensionful` scaling property and
Physlib's definition of `LengthUnit.centimeters` prove that the centimetre
readout is exactly 100 times the metre readout, yielding `12`.

## Verification

- Lean language-server diagnostics: no errors; only unused-hypothesis linter
  warnings for physical-role assumptions not needed after the supplied B.1
  and B.2 governing laws are used.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, added `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification reports only Lean/Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint status

The proof environment for
`IPhO2026Problems.IPhO2026_2_B_3.radius_for_fivefold_power` is ready for
deterministic `\leanok` synchronization. The blueprint was not edited because
the prover role permits writes only to the assigned Lean file and this result
file.

## Redraft needed

None.
