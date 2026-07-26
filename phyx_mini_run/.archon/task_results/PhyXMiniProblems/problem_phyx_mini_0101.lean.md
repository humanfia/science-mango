# Autoformalization result: `problem_phyx_mini_0101.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSnellsLawAtAtmosphere setup` states Snell's law at the outer-space--atmosphere interface:
  `n_space * sin i = n_atmosphere * sin r`.
- `SatisfiesConcentricHorizonGeometry setup` states the figure-derived concentric-circle and tangent-ray geometry: the outer radius readout is `R + h`, and the tangent right triangle gives `sin r = R / (R + h)`.
- The same geometry interface states the meanings of the labelled deviation and apparent position: `delta = i - r`, the apparent solar altitude is zero at the horizon, and `delta = apparent altitude - true altitude`.
- `HasPhysicalAtmosphericParameters setup` supplies positivity and principal-branch conditions needed to recover `i` and `r` with `Real.arcsin`; it does not prescribe their values or the requested deviation.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- `MatchesStatedAtmosphereData setup` records exactly the printed numerical data: `h = 20 km`, outer-space index `1`, and atmospheric index `1.0003 = 10003/10000`.
- `AtmosphericHorizonSetup` preserves the figure labels `R`, `h`, `R + h`, the incoming and refracted ray angles, the labelled deviation `delta`, and the true/apparent solar altitudes.
- `UsesMeanEarthRadiusCalibration setup` separately records `R = 6371 km`. This is not printed in the problem or figure; it is an explicit standard mean-Earth-radius calibration needed to select a numerical answer.
- `AnswerChoice.angleDegrees` records all four displayed values, and `recordedAnswerChoice` retains the dataset's label A only as metadata.

### Current target conclusions

- `deviation_eq_predictedDeviationRadians` concludes the symbolic inverse-sine formula for `delta` from the geometric and Snell-law assumptions.
- `atmosphericRefractionMakesAnswerAClosest` concludes that `delta` equals the derived formula, is within `0.01 degrees` of choice A's `0.23 degrees`, and that A is at least as close as every displayed option.

## Goal-faithfulness audit

No current target conclusion is a premise. In particular:

- Neither the inverse-sine formula nor the numerical closeness/choice-A result occurs in `MatchesStatedAtmosphereData`, `UsesMeanEarthRadiusCalibration`, `HasPhysicalAtmosphericParameters`, `SatisfiesConcentricHorizonGeometry`, or `SatisfiesSnellsLawAtAtmosphere`.
- `predictedDeviationRadians` only names the expression derived from the two independent ray angles; `setup.deviationAngleRadians` remains a separate field, so the equality between them is not true by unfolding.
- The fields `deviationIsRayBending` and `deviationSeparatesApparentAndTruePositions` give the physical/figure meaning of `delta`, not its requested numerical value or inverse-sine expression.
- `recordedAnswerChoice` is not passed to either theorem. The result selects A from the physical model plus the explicitly separated Earth-radius calibration, rather than assuming the recorded label.
- The missing numerical Earth radius is not silently attributed to the source. The calibrated multiple-choice theorem is conditional on `UsesMeanEarthRadiusCalibration`; the symbolic lemma remains independent of that calibration.

## Declarations created

The covered blueprint contains one declaration environment, `thm:physics:phyx_mini_0101:target`. Its main Lean declaration is:

- `PhyXMiniProblems.ProblemPhyXMini0101.atmosphericRefractionMakesAnswerAClosest` — `thm:physics:phyx_mini_0101:target`.

Supporting public declarations required to state that target faithfully are:

- Dimensional/readout layer: `DimLength`, `lengthValueIn`, `lengthInKilometers`, `radiansToDegrees`.
- Figure vocabulary: `OpticalRegion`, `SolarPosition`, `AtmosphericHorizonSetup`.
- Premise interfaces: `MatchesStatedAtmosphereData`, `UsesMeanEarthRadiusCalibration`, `HasPhysicalAtmosphericParameters`, `SatisfiesConcentricHorizonGeometry`, `SatisfiesSnellsLawAtAtmosphere`.
- Derived-expression and option vocabulary: `predictedDeviationRadians`, `AnswerChoice`, `AnswerChoice.angleDegrees`, `recordedAnswerChoice`, `MatchesWithinHundredthDegree`, `IsClosestAnswerChoice`.
- Symbolic supporting result: `deviation_eq_predictedDeviationRadians`.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `Snell's law refraction refractive index sine incidence angle`: returned `Real.Angle.sin`, `Real.sin`, and geometric law-of-sines declarations, but no Snell/refraction law.
- Natural-language query `atmospheric refraction apparent position horizon tangent ray`: returned generic `RayVector`, `Module.Ray`, `EuclideanGeometry.Sphere.IsTangentAt`, and right-triangle tangent lemmas, but no atmospheric-optics model compatible with the problem.
- Likely-name queries `Snell`, `SnellsLaw`, and `refractiveIndex`: returned no matching Physlib optics API.
- Natural-language queries `Dimensionful WithDim physical length LengthUnit kilometers`, `physical dimensionful length quantity`, and likely-name queries `DimLength`, `WithDim Dimension.L𝓭`, `LengthUnit.kilometers`, `UnitChoices.SI`: grounded `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit.kilometers`, and `UnitChoices.SI`.
- Query `Real.arcsin inverse sine radians degrees`: grounded `Real.arcsin` and `Real.sin`.
- Source was fetched for the candidates actually retained: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit.kilometers`, `UnitChoices.SI`, `Real.sin`, and `Real.arcsin`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit`, `LengthUnit.kilometers`, `UnitChoices`, `UnitChoices.SI`.
- Mathlib: `Real.sin`, `Real.arcsin`, `Real.pi`, and real absolute value notation.

`Dimensionful (WithDim Dimension.L𝓭 ℝ)` is used for physical radii and height. Kilometer and angle values are explicitly named scalar readouts, rather than replacing physical length with a transparent scalar alias.

## Local abstractions introduced

- `DimLength` is a local name for the grounded Physlib dimensionful-length construction, not an alias to `ℝ`.
- `OpticalRegion`, `SolarPosition`, and `AtmosphericHorizonSetup` preserve the roles of media, ray angles, solar positions, and labelled physical lengths shown in the figure.
- The premise structures separate source data, extra numerical calibration, admissibility/branch conditions, and figure geometry.
- `SatisfiesSnellsLawAtAtmosphere` is the smallest local governing-law predicate needed after LeanExplore found no ready-made optics API.
- The answer-choice definitions preserve the dataset options and express closeness without assuming the recorded answer.

## Source/law/answer audit

- Source: the formalization records `n = 1.0003`, `h = 20 km`, all four choices, and the figure labels/geometry. The primary image confirms the horizontal ray tangent to Earth and the entry radius `R + h`.
- Law: the local interface states Snell's law directly; no final answer is hidden in it.
- Answer: with the additional `R = 6371 km` calibration, the model predicts approximately `0.2222 degrees`, making `0.23 degrees` the closest displayed choice and placing it within `0.01 degrees`. Without an Earth-radius value, only the symbolic formula is determined.

## Grounding gaps and redraft requests

- No matching Mathlib/Physlib declaration for Snell's law, refractive index, or atmospheric refraction was found; the local predicate is therefore retained.
- The source and figure label `R` but do not supply its numerical value. The blueprint should be redrafted to state the intended Earth-radius approximation if a closed numerical multiple-choice conclusion is desired. Until then, the calibrated theorem is correctly conditional and the symbolic lemma is the source-supported result.
- `.archon/AGENTS.md` and the advertised `archon` executable are absent in this checkout. The supplied task instructions and `.archon/prover-modes/physics-formalize.md` were used for the role/workflow; consequently the dependency DAG could not be queried.
- The blueprint environment was not edited with `\leanok` because this task's explicit write permissions prohibit editing blueprint chapters. The target Lean declaration is present and compiles.

## Verification

`archon-lean-lsp` reports no errors. The only diagnostics are the two expected `declaration uses sorry` warnings on the symbolic lemma and target theorem, as required by physics-autoformalize mode.
