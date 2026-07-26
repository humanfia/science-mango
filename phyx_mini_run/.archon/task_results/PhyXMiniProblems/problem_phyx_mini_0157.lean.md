# Autoformalization result: `phyx_mini_0157`

The chapter contains `% archon:physics`, so this retry followed the
`physics-formalize` discipline. The review gate's exact complaint was that the
target did not explicitly import Mathlib. The assigned file now imports
`Mathlib` and retains the complete physical formalization described below.

## Assumption/target split

### Governing laws

- `SatisfiesConstantVolumeIdealGasThermometry` states, independently for the
  reference and measuring bulbs, that pressure is proportional to absolute
  temperature while gas amount and volume are fixed. The relations are
  cross-multiplied, so they introduce no unit-dependent proportionality
  constant.
- The same structure states that the signed manometer readout is measuring-bulb
  pressure minus reference-bulb pressure. This fixes a sign convention that the
  source's phrase “pressure difference” leaves implicit.
- `HasPhysicalGasThermometerParameters` selects the physical branch by requiring
  positive fixed SI volume, positive mole readout, and positive absolute
  temperatures.

### Previous-part results

- None. The source report's `previous_parts` array is empty, and the blueprint
  presents a standalone multiple-choice problem.

### Figure/data readouts

- `HasGasThermometerCalibrationData` records the problem's intended
  textbook-scale calibration values `273 K` and `373 K`.
- It records zero signed pressure difference when both bulbs are at the triple
  point, `120 torr` when the measuring bath is at the boiling point, and
  `90 torr` when the measuring bath is at the unknown temperature.
- The actual raster `phyx_data/test_image/157.png` is not a gas-thermometer
  diagram. It shows critical-angle rays in water and labels `Air, n₂ = 1.00`,
  `Water, n₁ = 1.33`, `h = 3.0 m`, `D`, `R`, and `θ_c`. Those unrelated optics
  labels are not asserted as gas-thermometer data. The Lean module documentation
  records this source mismatch explicitly.

### Current target conclusion

- `unknownTemperature_eq_348_kelvin` concludes only that the unknown
  temperature's calibrated absolute-temperature readout is `348` K, matching
  answer choice D.

## Goal-faithfulness audit

The `348 K` conclusion occurs only in the conclusion of
`unknownTemperature_eq_348_kelvin`. It is absent from
`TwoBulbGasThermometer`, `HasPhysicalGasThermometerParameters`,
`SatisfiesConstantVolumeIdealGasThermometry`, and
`HasGasThermometerCalibrationData`; no local definition unfolds to the target.
The data premises contain only source/calibration values (`273`, `373`, `0`,
`120 torr`, and `90 torr`) and the law premises contain only the constant-volume
ideal-gas and differential-pressure relations.

The physical route remains substantive: equality of the two bulb pressures at
`273 K` makes their pressure/temperature proportionality factors equal; hence
the signed differential pressure is proportional to the measuring bath's
temperature rise above `273 K`. Comparing `90 torr` with `120 torr` gives a
temperature rise of `(90 / 120) * (373 - 273) = 75 K`, hence `348 K`.

## Physical model and declarations

- `GasVolume`: a dimensionful length-cubed quantity,
  `Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)`.
- `ConstantVolumeGasBulb`: fixed physical volume plus an explicitly named
  scalar mole readout.
- `TwoBulbGasThermometer`: the two bulbs, the three absolute temperatures,
  each bulb's pressure response, and the signed manometer response.
- `HasPhysicalGasThermometerParameters`: positivity assumptions.
- `SatisfiesConstantVolumeIdealGasThermometry`: governing-law interface.
- `HasGasThermometerCalibrationData`: standard temperature calibration and
  experimental manometer readouts.
- `unknownTemperature_eq_348_kelvin`: declaration corresponding to blueprint
  label `thm:physics:phyx_mini_0157:target`.

These helper declarations are public because each names a distinct physical
role needed by the assumption/target split. No extra public numerical lemma was
introduced.

## LeanExplore queries and candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query: `constant-volume ideal gas law pressure proportional
  to absolute temperature gas thermometer`.
  - Candidate `IdealGas.ideal_gas_law` from
    `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` was inspected.
    Its source states `P * V = n * R * T` in a unitless system with `R = 1`.
    This is a near miss: it does not express two independent dimensionful bulb
    pressures or a mercury-manometer difference, so it was not imported as the
    governing-law interface.
  - Candidates `Temperature`, `Temperature.toReal`, `DimPressure`, and
    `Dimensionful` were relevant and are used.
- Likely-name query: `Temperature Kelvin thermodynamics`.
  - `Temperature` and `Temperature.toReal` from
    `Physlib.Thermodynamics.Temperature.Basic` ground absolute temperature and
    its calibrated real readout.
  - `TemperatureUnit.kelvin` and `UnitChoices.SI_temperature` were returned but
    are not needed because this problem records the Kelvin calibration directly
    on the `Temperature.toReal` readouts.
- Likely-name query: `DimPressure torr pressure dimensionful`.
  - `DimPressure` and `DimPressure.torr` from
    `Physlib.Units.WithDim.Pressure` are used for pressure-valued functions and
    the two observed torr differences.
  - `Dimensionful` from `Physlib.Units.Basic` grounds the fixed-volume type.

## Physlib/Mathlib names grounded

- `Temperature`
- `Temperature.toReal`
- `DimPressure`
- `DimPressure.torr`
- `Dimensionful`
- `WithDim`
- `UnitChoices` and `UnitChoices.SI`
- dimension symbols `L𝓭`

The file explicitly imports `Mathlib` to satisfy the retry gate and is checked
inside the Lake project rather than as a standalone Lean smoke file.

## Local abstractions introduced

Physlib has no ready-made two-bulb constant-volume gas thermometer or signed
mercury-manometer apparatus. The local bulb/setup structures preserve those
physical roles. The local governing-law structure uses dimensional pressure at
every unit choice and calibrated absolute-temperature readouts, avoiding a
scalar alias for pressure or volume. It also keeps governing laws separate from
observed data and the current answer.

## Source/law/answer audit

- Source text: two fixed-volume bulbs; zero difference at the triple point;
  `120 torr` across triple/boiling temperatures; `90 torr` across
  triple/unknown temperatures.
- Law: at fixed gas amount and volume, each pressure is proportional to absolute
  temperature; the manometer reads the signed pressure difference.
- Supported answer: `348 K`, choice D.
- Image: unrelated critical-angle optics diagram, so it supplies no trustworthy
  thermometer dimensions or labels.

## Grounding gaps and redraft requests

- `IdealGas.ideal_gas_law` is unitless and not signature-compatible with this
  dimensional two-bulb setup; the local law interface is therefore necessary.
- The blueprint chapter exists and has the target environment, but its proof
  paragraph gives only the autoformalization directive rather than the informal
  derivation above. A plan-agent redraft should add that derivation and note the
  source-image mismatch.
- The blueprint was not edited to add `\leanok` because this task's explicit
  write permissions prohibit blueprint edits. A blueprint-authorized agent
  should add the marker after accepting the declaration.
- The requested `.archon/AGENTS.md` is absent; the available
  `.archon/prover-modes/physics-formalize.md` was used as the role document.
- The assigned Lean file contains no `/- USER: ... -/` comments.
- Although the prompt says `archon` is on `PATH`, the executable is unavailable
  in this runtime, so the optional DAG queries could not be run.

## Validation

- Lean LSP before the retry edit reported only the expected `declaration uses
  sorry` warning.
- Final validation with `lake env lean
  PhyXMiniProblems/problem_phyx_mini_0157.lean` exited successfully and emitted
  only the mandated `declaration uses sorry` warning at the target theorem.
- Final Lean LSP diagnostics likewise report only that warning, with no errors
  or failed dependencies.
