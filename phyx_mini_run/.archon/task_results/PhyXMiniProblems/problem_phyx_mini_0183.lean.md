# Prover result: problem_phyx_mini_0183

## Completed

- Proved `markedSpan_is_three_halfWavelengths` by telescoping the three
  adjacent cork-pile intervals from `pile1` through `pile4`.
- Proved `standingWavelengthInOxygen_meters_eq`, deriving the exact
  `centimetersValue = 100 * metersValue` conversion from the
  `Dimensionful` unit-scaling law and obtaining the wavelength `41 / 50 m`.
- Proved `speedOfSoundInOxygen_is_328_metersPerSecond` from `v = λ f`,
  the `400 Hz` readout, and the derived `0.82 m` wavelength; the recorded
  answer choice reduces to `D = 328 m/s`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0183.lean` succeeds.
- The assigned file contains no `sorry`, `admit`, or introduced `axiom`.
- Axiom verification reports only standard imported axioms:
  `propext`, `Classical.choice`, and `Quot.sound`.
- The sole compiler warning is the frozen, unused `h_physical` hypothesis
  in `standingWavelengthInOxygen_meters_eq`.

## Blueprint

The chapter already exists. It was not edited because prover write
permissions restrict this task to the assigned Lean file and this result
file.

## Redraft needed

None.
