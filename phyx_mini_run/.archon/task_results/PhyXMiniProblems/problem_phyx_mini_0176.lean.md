# Physics autoformalization result: `problem_phyx_mini_0176.lean`

The review gate rejected this target only because no genuine
post-formalization task result existed. I re-audited the current Lean model
against the source report, primary image, blueprint, and fresh LeanExplore
results. The statement is physically faithful, so it was preserved without
public-declaration additions, removals, or signature changes.

## Assumption/target split

### Governing laws

- `SatisfiesStandingWaveLaws.fixedEndpointHarmonicGeometry` states the generic
  fixed-end mode relation `2 L = n λ`, where `n` is the number of visible
  antinodal loops (half-wavelength intervals). It does not fix `L`, `n`, or
  `λ` to the values in this problem.
- `SatisfiesStandingWaveLaws.waveSpeedFrequencyWavelengthRelation` states the
  generic propagation law `v = f λ`. It does not fix the requested speed.
- `HasPhysicalStandingWaveParameters` supplies positivity and nondegeneracy
  for the span, wavelength, frequency, speed, and loop count. None of its
  fields assigns a requested numerical value.
- The meter/centimeter relation is exposed as the supporting conclusion
  `lengthInMeters_eq_lengthInCentimeters_div_hundred`, grounded in the
  Physlib unit representation rather than assumed in the problem premises.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemAndFigureReadouts.mediumIsString` and `waveIsStanding` retain
  the prose/figure classification as a transverse standing wave on a string.
- `leftBoundaryFixed`, `rightBoundaryFixed`, `leftEndpointNode`, and
  `rightEndpointNode` retain the two shaded fixed supports and endpoint nodes.
- `supportSeparationCentimeters` records the image's dimension arrow as
  `L = 60 cm`.
- `frequencyHertz` records the prose datum `f = 100 Hz`.
- `visibleLoopCount` records the four closed antinodal loops visible in the
  primary image. Thus the span comprises four half-wavelength intervals.
- `displayedAnswerSpeedInMetersPerSecond` retains all printed choices
  (`15`, `60`, `50`, and `30 m/s`), while `recordedDatasetAnswer` retains D as
  metadata. Neither is a physical premise of the theorem.

### Current target conclusions

- `lengthInMeters_eq_lengthInCentimeters_div_hundred` concludes the general
  meter/centimeter readout conversion for a dimensionful length.
- `wavelength_is_three_tenths_meter` concludes `λ = 3/10 m` from the four-loop
  fixed-end geometry and the `60 cm` span.
- `problem_phyx_mini_0176` concludes `v = 30 m/s` and that this independently
  modeled speed matches displayed answer choice D.

## Goal-faithfulness audit

`StandingWaveOnStringSetup.wavelength` and `propagationSpeed` are independent
dimensionful fields. Neither is defined from the source numbers, the answer
choice, or the desired result. `MatchesProblemAndFigureReadouts` contains only
the qualitative fixed-string facts and direct readouts `60 cm`, `100 Hz`, and
four loops. It contains neither `λ = 0.30 m` nor `v = 30 m/s`.

`SatisfiesStandingWaveLaws` contains only the uniform textbook relations
`2 L = n λ` and `v = f λ`; it does not specialize them to this image or state
either target value. Positivity likewise does not determine a value. The
derived wavelength appears only as a lemma conclusion, not as a premise of the
main theorem.

`MatchesAnswerChoice` is a generic comparator between an independently modeled
physical speed and a displayed metadata value. It occurs only in the theorem
conclusion. Although choice D unfolds to `30`, this cannot prove the predicate
without first deriving the setup's speed. `recordedDatasetAnswer` is not used
as a hypothesis. Therefore no current target conclusion is smuggled into a
premise structure, governing-law field, or local definition.

## Source/law/answer audit

- Blueprint mode marker confirmed: `% archon:physics`.
- Source report inspected:
  `reports/phyx_mini/problem_phyx_mini_0176.source.json`. It states a string
  standing wave at `100 Hz`, lists the four speeds, records answer D, and has
  no previous parts.
- Primary image inspected: `phyx_data/test_image/176.png`. It visibly shows
  two shaded supports, endpoint nodes, four antinodal loops, and a `60 cm`
  support-to-support arrow.
- The auxiliary machine caption's claim of three complete wavelengths is
  inconsistent with the bitmap. Four loops represent four half-wavelengths,
  i.e. two complete wavelengths, so the caption claim is not formalized as a
  readout.
- From `2L = nλ`, `L = 0.60 m`, and `n = 4`, one obtains
  `λ = 2(0.60)/4 = 0.30 m`. Then `v = fλ = 100(0.30) = 30 m/s`, supporting
  displayed and recorded choice D.
- No `/- USER: ... -/` file-specific hint occurs in the assigned Lean file.

## Declarations and blueprint correspondence

The following declaration set was audited and preserved:

- Dimensionful quantities:
  `LengthQuantity` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-lengthquantity`),
  `FrequencyQuantity` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-frequencyquantity`), and
  `SpeedQuantity` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-speedquantity`).
- Unit readouts:
  `lengthReadout` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-lengthreadout`),
  `frequencyReadout` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-frequencyreadout`),
  `speedReadout` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-speedreadout`),
  `lengthInMeters` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-lengthinmeters`),
  `lengthInCentimeters` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-lengthincentimeters`),
  `frequencyInHertz` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-frequencyinhertz`), and
  `speedInMetersPerSecond` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-speedinmeterspersecond`).
- Physical/figure labels:
  `StringEndpoint` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-stringendpoint`),
  `StringBoundaryCondition` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-stringboundarycondition`),
  `StringWaveKind` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-stringwavekind`), and
  `WaveMediumKind` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-wavemediumkind`).
- Setup and premise split:
  `StandingWaveOnStringSetup` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-standingwaveonstringsetup`),
  `MatchesProblemAndFigureReadouts` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-matchesproblemandfigurereadouts`),
  `HasPhysicalStandingWaveParameters` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-hasphysicalstandingwaveparameters`), and
  `SatisfiesStandingWaveLaws` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-satisfiesstandingwavelaws`).
- Answer metadata:
  `AnswerChoice` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-answerchoice`),
  `displayedAnswerSpeedInMetersPerSecond` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-displayedanswerspeedinmeterspersecond`),
  `recordedDatasetAnswer` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-recordeddatasetanswer`), and
  `MatchesAnswerChoice` (`def:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-matchesanswerchoice`).
- Supporting conclusions:
  `lengthInMeters_eq_lengthInCentimeters_div_hundred` (`lem:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-lengthinmeters-eq-lengthincentimeters-div-hundred`) and
  `wavelength_is_three_tenths_meter` (`lem:physics:phyx-mini-0176:phyxminiproblems-problemphyxmini0176-wavelength-is-three-tenths-meter`).
- Main theorem `problem_phyx_mini_0176` corresponds to
  `thm:physics:phyx_mini_0176:target`.

## LeanExplore queries/candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query
  `standing wave on a fixed string nodes antinodal loops wavelength wave speed frequency`
  returned general `ClassicalMechanics.WaveEquation`,
  `ClassicalMechanics.harmonicWave`, and
  `ClassicalMechanics.transverseHarmonicPlaneWave` candidates, but no
  fixed-end string normal-mode API with discrete loop counts.
- Natural-language query `speed equals frequency times wavelength` returned
  `DimSpeed` (id 394481) and the near-match `UnitExamples.SpeedEq`; the latter
  is a dimensional speed-distance-time example, not the string-wave law
  `v = f λ`.
- Natural-language fixed-mode query
  `standing wave fixed endpoints harmonic geometry 2 L equals n lambda`
  again returned only general harmonic/plane-wave declarations. This grounds
  the need for the local `SatisfiesStandingWaveLaws` interface.
- Likely-name query `Dimensionful WithDim physical quantity UnitChoices`
  selected `Dimensionful` (id 394284),
  `instCoeFunDimensionfulForallUnitChoices` (id 394285), and the surrounding
  unit-choice infrastructure.
- Likely-name query
  `WithDim Dimension.L𝓭 Dimension.T𝓭 TimeUnit.seconds LengthUnit.meters`
  selected `WithDim` (id 394425), `Dimension.L𝓭` (id 394324), and
  `Dimension.T𝓭` (id 394330).
- Likely-name/unit queries `DimSpeed LengthUnit centimeters TimeUnit seconds`,
  `TimeUnit.seconds`, and `length unit of meters` selected `DimSpeed`
  (id 394481), `LengthUnit` (id 393137), `LengthUnit.meters` (id 393154),
  `LengthUnit.centimeters` (id 393160), `TimeUnit.seconds` (id 393630), and
  `UnitChoices.SI` (id 394270).
- Likely-name query `instCoeFunDimensionfulForallUnitChoices` selected the
  coercion instance (id 394285) used implicitly when evaluating a
  `Dimensionful` quantity at a `UnitChoices` value.
- Natural-language/likely-type query `NNReal nonnegative real numbers`
  selected Mathlib's `NNReal` (id 211536).

Source and module lookups were fetched for every selected declaration named
above. No source lookup was used merely as decoration for rejected candidates.

## Physlib/Mathlib names grounded

- `Dimensionful`, `UnitChoices.SI`, and
  `instCoeFunDimensionfulForallUnitChoices` from `Physlib.Units.Basic`.
- `WithDim` and its `val` projection from `Physlib.Units.WithDim.Basic`.
- `DimSpeed` from `Physlib.Units.WithDim.Speed`; its fetched source is
  `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.
- `LengthUnit`, `LengthUnit.meters`, and `LengthUnit.centimeters` from
  `Physlib.SpaceAndTime.Space.LengthUnit`; the fetched centimeter definition
  is a `10⁻²` scaling of meters.
- `TimeUnit.seconds` from `Physlib.SpaceAndTime.Time.TimeUnit`.
- `Dimension.L𝓭` and `Dimension.T𝓭` from `Physlib.Units.Dimension`.
- `NNReal` from `Mathlib.Data.NNReal.Defs`; real and natural number arithmetic
  is available through the explicit `Mathlib` import.

## Local abstractions introduced

- `LengthQuantity` and `FrequencyQuantity` are not scalar placeholders. They
  are Physlib `Dimensionful` quantities carrying length and inverse-time
  dimensions with nonnegative values. `SpeedQuantity` directly reuses
  Physlib's `DimSpeed`.
- The readout functions are explicit projections in selected units. Real
  numbers occur only after choosing meters, centimeters, seconds, or their
  combinations; the physical quantities remain unit-independent.
- The four small enums preserve distinct roles for the two endpoints, boundary
  condition, disturbance type, and material medium.
- `StandingWaveOnStringSetup` is the smallest local setup retaining the
  independent physical quantities and figure labels needed by the problem.
- `MatchesProblemAndFigureReadouts`, `HasPhysicalStandingWaveParameters`, and
  `SatisfiesStandingWaveLaws` keep source data, nondegeneracy, and governing
  laws separate. The fixed-end string normal-mode law is local because the
  searched libraries provide only general wave/plane-wave APIs.
- The answer-choice definitions retain printed metadata separately from the
  physical model and do not determine the setup's propagation speed.

## Grounding gaps and redraft requests

- Mathlib/Physlib provides suitable dimensional quantity and unit
  infrastructure, but LeanExplore found no matching fixed-fixed string
  standing-wave normal-mode declaration with endpoint nodes, antinodal-loop
  count, and `2 L = n λ`. The local law/setup abstractions are therefore
  necessary.
- No semantic redraft is requested. The primary image, laws, symbolic
  derivation, numerical result, and recorded choice D agree.
- The requested `.archon/AGENTS.md` is absent from this checkout. The injected
  role instructions, complete `.archon/PROGRESS.md`, and
  `.archon/prover-modes/physics-formalize.md` were followed; the archived role
  file was consulted for the same prover permission discipline.
- The blueprint was not edited because the explicit write-permission section
  permits edits only to the assigned Lean file and this task-result file and
  explicitly forbids prover edits to blueprint chapters. Marker synchronization
  should apply `\\leanok` after accepting the compiling declaration.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly three expected
  `declaration uses sorry` warnings, for the unit conversion lemma, wavelength
  lemma, and main theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0176.lean` exited with
  status 0 and the same three expected warnings.

