# Autoformalization result: `problem_phyx_mini_0500.lean`

## Status

Redrafted and audited the assigned physics-formalize stub. It compiles with four expected `sorry` warnings and no errors. The chapter contains `% archon:physics`, and the main theorem covers blueprint label `thm:physics:phyx_mini_0500:target`.

The requested `.archon/AGENTS.md` is absent in this run. I followed the injected prover instructions, `.archon/PROGRESS.md`, and `.archon/prover-modes/physics-formalize.md`. The assigned file contains no `/- USER: ... -/` comments. I also inspected the primary `504 × 280` image directly.

The retry gate's exact reason was missing post-formalization evidence. This report records searches and modeling decisions made against the completed Lean model.

## Assumption/target split

### Governing laws

- `SatisfiesNeutronInterferenceLaws.linearFigureCalibration`: a physical detector spacing is calibrated from the adjacent central-peak pixel separation relative to the printed `100 μm` scale bar.
- `SatisfiesNeutronInterferenceLaws.paraxialAdjacentFringeLaw`: adjacent paraxial double-slit maxima satisfy `Δy d = L λ` in any common length unit.
- `SatisfiesNeutronInterferenceLaws.deBroglieMatterWaveLaw`: the selected scalar matter-wave model satisfies `λ m v = h` in SI readouts.
- `HasPhysicalNeutronInterferenceParameters`: positivity of the physical lengths, mass, action, and speed. It supplies no numerical target value.

### Previous-part results

- None. The source report has an empty `previous_parts` list, and the blueprint declares no dependencies.

### Figure/data and reference readouts

- `MatchesNeutronDoubleSlitScenario`: neutron species, two narrow parallel slits, transmitted-neutron detection, and the paraxial/nonrelativistic textbook regime.
- `MatchesProblemLengthReadouts`: the literal source values `d = 0.10 nm` and `L = 3.5 m`.
- `MatchesSuppliedDetectorFigure`: detector-position and neutron-intensity axis roles; the absent horizontal label and present vertical label; the symmetric resolved-peak envelope; rounded peak coordinates `223`, `256`, and `288`; scale-bar endpoints `385` and `433`; and the printed `100 μm` length.
- `UsesStandardNeutronReferenceData`: neutron mass `1.67492749804e-27 kg` and ordinary Planck action `2πℏ`, using Physlib's reduced Planck constant.
- `displayedSpeedInMetersPerSecond` and `recordedDatasetAnswer`: the source's displayed choices and recorded label C. These are metadata only and do not assert that C matches the modeled speed.

### Current target conclusions

- `adjacent_fringe_spacing_micrometers_eq`: adjacent central-fringe spacing `200/3 μm`.
- `matter_wavelength_femtometers_eq`: matter wavelength `40/21 fm`.
- `neutron_speed_in_literal_data_rounding_interval`: `150000000 ≤ v < 250000000 m/s`, the interval rounding to `2 × 10^8 m/s` at one significant figure.
- `problem_phyx_mini_0500`: both intermediate values, the literal-data speed interval, `RoundsToOneSignificantFigure v 200000000`, and the fact that no displayed answer choice matches.

## Goal-faithfulness audit

The fringe spacing, wavelength, speed interval, one-significant-figure result, and failure of the displayed choices occur only as lemma or theorem conclusions. They do not occur in the scenario, positivity, source-data, figure-data, reference-data, or governing-law structures.

`adjacentBrightFringeSpacing`, `matterWavelength`, and `neutronSpeed` are independent physical fields of `NeutronDoubleSlitSetup`; none is defined from an answer value. The calibration, double-slit, and de Broglie fields are generic laws and do not specialize these observables to the current numerical results. `RoundsToOneSignificantFigure` is a generic relation based on Mathlib's `round`; unfolding it cannot establish the modeled speed.

Choice C's displayed `200 m/s` and the recorded label C are necessarily present as source metadata, but no hypothesis says that either matches the neutron speed. The main conclusion instead records the physically supported `2 × 10^8 m/s` result and proves no displayed choice matches. Thus the inconsistent dataset answer was not smuggled into a premise or silently treated as a law.

Real scalars are restricted to calibrated unit readouts, dimensionless raster coordinates, numerical reference readouts, and displayed/reporting values. Physical lengths, mass, action, and speed remain Physlib `Dimensionful` quantities.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0500:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0500.problem_phyx_mini_0500`.
- Supporting target lemmas are `adjacent_fringe_spacing_micrometers_eq`, `matter_wavelength_femtometers_eq`, and `neutron_speed_in_literal_data_rounding_interval`.
- Physical quantity/readout declarations are `LengthQuantity`, `MassQuantity`, `actionDimension`, `ActionQuantity`, `lengthReadout`, the named length readouts, `massInKilograms`, `speedInMetersPerSecond`, and `actionInJouleSeconds`.
- Experimental vocabulary/model declarations are `ParticleSpecies`, `SlitArrangement`, `PropagationRegime`, `PlotAxis`, `PlotAxisRole`, `FigureLandmark`, `NeutronDetectorFigure`, and `NeutronDoubleSlitSetup`.
- Premise interfaces are `MatchesNeutronDoubleSlitScenario`, `MatchesProblemLengthReadouts`, `MatchesSuppliedDetectorFigure`, `UsesStandardNeutronReferenceData`, `HasPhysicalNeutronInterferenceParameters`, and `SatisfiesNeutronInterferenceLaws`.
- Source-answer/reporting declarations are `AnswerChoice`, `displayedSpeedInMetersPerSecond`, `recordedDatasetAnswer`, `RoundsToOneSignificantFigure`, and `MatchesDisplayedSpeed`.

The theorem environment is ready for `\leanok` at the autoformalization level. I did not edit the blueprint because the explicit write permissions allow only the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

Every query used package filters `Mathlib` and `Physlib`.

- `Dimensionful WithDim LengthUnit DimSpeed`: returned and grounded `Dimensionful` and `DimSpeed`; it also returned unit-scaling declarations.
- `Planck constant reduced Planck constant ℏ`: returned and grounded `Constants.ℏ`.
- `de Broglie matter wavelength momentum`: returned `Momentum` and momentum-operator declarations, but no scalar de Broglie wavelength law suitable for this experiment.
- `double slit interference adjacent bright fringe spacing`: returned unrelated complex-analysis and adjacent-interval declarations, with no double-slit interference law.
- `WithDim LengthUnit MassUnit UnitChoices`: returned and grounded `UnitChoices` and `LengthUnit` plus unit-scaling declarations.
- `MassUnit kilograms Physlib`: returned and grounded `MassUnit.kilograms` and `UnitChoices.SI`.
- `round real number to nearest integer round`: returned and grounded Mathlib's `round`.

Source code and module information were fetched for the candidates used:

- `Dimensionful` — `Physlib.Units.Basic`; its source is the subtype of unit-choice functions satisfying `HasDimension`.
- `DimSpeed` — `Physlib.Units.WithDim.Speed`; its source is `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `Constants.ℏ` — `Physlib.QuantumMechanics.PlanckConstant`; its source gives the positive joule-second readout `1.054571817e-34`.
- `LengthUnit` — `Physlib.SpaceAndTime.Space.LengthUnit`.
- `UnitChoices` — `Physlib.Units.Basic`.
- `MassUnit.kilograms` — `Physlib.ClassicalMechanics.Mass.MassUnit`.
- `round` — `Mathlib.Algebra.Order.Round`; its source specifies nearest-integer rounding with ties toward positive infinity.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `MassUnit.kilograms`, `DimSpeed`, and `Constants.ℏ`.
- Mathlib: `NNReal`, `Real.pi`, and `round`.

All of these names were additionally checked by successful Lean elaboration of the assigned file.

## Local abstractions introduced

- `ActionQuantity` instantiates Physlib's dimensionful machinery at `M L² T⁻¹`; action is not reduced to a scalar alias.
- The particle, slit, approximation-regime, graph-axis, and landmark inductives preserve experimental and geometric roles for which no suitable library type was found.
- `NeutronDetectorFigure` separates the physical scale-bar length from dimensionless raster coordinates and qualitative trace properties.
- `NeutronDoubleSlitSetup` keeps inferred spacing, wavelength, and speed as independent observables rather than definitions from the answer.
- `SatisfiesNeutronInterferenceLaws` supplies the unavailable experiment-specific calibration, paraxial double-slit, and scalar de Broglie relations as governing-law hypotheses.
- `RoundsToOneSignificantFigure` supplies the unavailable reporting relation using Mathlib's grounded `round` operation.

## Grounding gaps

- LeanExplore exposed no ready-made adjacent-fringe double-slit law, scalar de Broglie wavelength law, raster-calibration interface, unit-independent neutron-mass constant, or significant-figure reporting relation. Faithful local abstractions were therefore required.
- The `archon` executable is not available on `PATH`, so the optional dependency-graph commands could not run. The blueprint itself has no `\uses` entries, and the source report lists no previous parts.
- `.archon/AGENTS.md` is absent; the injected instructions and checked-in physics-formalize mode supplied the role discipline.

## Source/law/answer audit and redraft note

The primary image supports an adjacent peak separation of about `32 px` and a `48 px` scale bar, hence
`Δy = 100 μm × 32/48 = 200/3 μm`. With the literal `d = 0.10 nm` and `L = 3.5 m`, the paraxial law gives `λ = 40/21 fm`. Using the stated neutron mass and `h = 2πℏ` then gives approximately `207691785.5 m/s`, which rounds to `200000000 m/s` at one significant figure.

This is not the recorded `200 m/s`, and none of the four displayed values matches. In accordance with the retry protocol, the formalization retains C only as dataset metadata and states the physically supported result. If C was intended as physically correct, the likely source typo is `0.10 mm` rather than `0.10 nm`; correcting the source to millimetres would yield a speed near `208 m/s`.
