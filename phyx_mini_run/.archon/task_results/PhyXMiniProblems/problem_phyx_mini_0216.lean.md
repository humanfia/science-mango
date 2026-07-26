# Autoformalization result: `problem_phyx_mini_0216.lean`

## Assumption/target split

### Governing laws

- `SourceDistancesFollowFigureGeometry.distance_is_euclidean` connects each
  dimensionful source-to-listener path length, via its SI-metre readout, to
  the `Space 2` Euclidean distance between the source and the corresponding
  listener. It does not state either derived distance or their ratio.
- `SatisfiesIsotropicInverseSquareLaw.inverseSquare` states the general
  isotropic-source law `4 * pi * r^2 * I = P` for both listeners and every
  coherent unit choice. The common power field represents the one explosion;
  the law contains no factor-five or decibel result.
- `directlyBelowSoundLevelAdvantageInDecibels` states the general sound
  intensity-level comparison `10 * log10 (I_direct / I_displaced)`.
- `MatchesFireworksScenario` records the idealized fireworks-shell source,
  ambient-air propagation, and isotropic spherical free-field spreading.
- `HasPhysicalAcousticParameters` supplies positive power, lengths, and
  intensities so divisions and logarithmic ratios have the intended physical
  meaning.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesSuppliedFigure` assigns the physical roles of the fireworks shell,
  the directly-below person, and the horizontally displaced person.
- It records the figure's 100 m shell height and 200 m horizontal listener
  separation as SI readouts of dimensionful lengths.
- It places the shell at `(0, 100)`, the near listener at `(0, 0)`, and the
  displaced listener at `(200, 0)` in the depicted vertical cross-section,
  expressed parametrically through the two dimensionful readouts.
- `displayedSoundLevelDifferenceInDecibels` neutrally transcribes all four
  printed answer values: A = 13, B = 11, C = 9, and D = 7.

### Current target conclusions

- `displacedDistance_sq_eq_five_mul_directDistance_sq`: the squared slant
  distance is five times the squared vertical distance.
- `displacedIntensity_eq_oneFifth_directIntensity`: the displaced listener's
  acoustic intensity is one fifth of the directly-below listener's intensity.
- `problem_phyx_mini_0216`: the exact level advantage is
  `10 * Real.logb 10 5` and this agrees with choice D after rounding to the
  nearest whole decibel.

## Goal-faithfulness audit

The squared-distance factor five, one-fifth intensity conclusion, exact
logarithmic advantage, and selection of choice D occur only in derived lemma
or theorem conclusions. They do not occur in `FireworksSoundSetup`, the
scenario predicate, the figure predicate, the geometry-law structure, the
positivity predicate, or the inverse-square-law structure. Both distances and
both intensities remain independent setup fields until the governing geometry
and acoustics laws are applied.

The numeral 7 occurs in the neutral table that transcribes every supplied
answer choice. `MatchesAnswerToNearestWholeDecibel` is generic in a choice and
does not select D by unfolding. Likewise, the sound-level definition is the
general decibel conversion and contains no problem-specific ratio or answer.

Primitive physical quantities were not collapsed to scalar aliases. Length,
effective acoustic power, and acoustic intensity specialize Physlib's
unit-independent `Dimensionful` framework. Real numbers occur only as named
unit/coordinate readouts, the dimensionless logarithm argument, and the
decibel result.

## Declarations and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0216:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0216.problem_phyx_mini_0216`.
- Supporting derived declarations are
  `displacedDistance_sq_eq_five_mul_directDistance_sq` and
  `displacedIntensity_eq_oneFifth_directIntensity`.
- Supporting model declarations cover dimensionful lengths/power/intensity,
  SI and coherent-unit readouts, listener and figure labels, the `Space 2`
  layout, physical scenario, Euclidean distance bridge, positivity,
  inverse-square propagation, decibel comparison, and answer table.

## LeanExplore queries/candidates actually used

Every query used package filters `Mathlib` and `Physlib`.

- `sound intensity level in decibels logarithm of intensity ratio inverse
  square propagation`: selected `Real.logb`; no acoustic sound-level or
  inverse-square propagation declaration was returned.
- `Real.logb logarithm base ten`: confirmed `Real.logb` and nearby logarithm
  lemmas. Its source, docstring, and module were fetched; it is defined as
  `Real.log x / Real.log b` in
  `Mathlib.Analysis.SpecialFunctions.Log.Base`.
- `Euclidean distance Pythagorean theorem norm product coordinates` and
  `Space.dist_eq`: selected the Physlib `Space` distance instance and
  `Space.dist_eq`. The fetched source confirms
  `dist p q = sqrt (sum_i (p i - q i)^2)` in
  `Physlib.SpaceAndTime.Space.Basic`.
- `SI units length meter physical quantity dimensions`: selected
  `UnitChoices.SI`, `Dimension`, `LengthUnit`, and `Dimension.L𝓭` as the
  relevant dimensional infrastructure.
- `Dimensionful WithDim UnitChoices CarriesDimension.toDimensionful` and
  `Dimensionful physical quantity coherent units readout`: selected
  `Dimensionful` and its coherent-unit function coercion. Source/module/docs
  were fetched for `Dimensionful` and `UnitChoices.SI`.

## Physlib/Mathlib names grounded

- Mathlib: `Real.logb`, `Real.pi`, `NNReal`, `dist`, and real absolute value.
- Physlib: `Space`, `Space.dist_eq`, `Dimensionful`, `WithDim`,
  `UnitChoices`, `UnitChoices.SI`, and the physical dimension symbols `L𝓭`,
  `M𝓭`, and `T𝓭`.

## Local abstractions introduced

- `AcousticLength`, `AcousticPowerQuantity`, and
  `AcousticIntensityQuantity` specialize `Dimensionful` to dimensions `L`,
  `M L^2 T^-3`, and `M T^-3`, preserving the roles and SI meanings of metres,
  watts, and watts per square metre.
- `FireworksFigure` and its label/role enumerations preserve every physical
  object and the geometry shown in the image.
- `FireworksSoundSetup` keeps source properties, the two printed lengths,
  common effective emitted power, both path lengths, and both intensities
  distinct.
- `SourceDistancesFollowFigureGeometry` is a local bridge between physical
  lengths and metre-coordinate Euclidean geometry.
- `SatisfiesIsotropicInverseSquareLaw` supplies the unavailable general
  acoustic propagation law as a hypothesis interface.
- `directlyBelowSoundLevelAdvantageInDecibels` supplies the unavailable
  acoustic decibel conversion using grounded `Real.logb`.

## Grounding gaps and redraft requests

- LeanExplore exposed no Physlib abstraction for acoustic intensity, acoustic
  sound level/decibels, fireworks sound, or isotropic acoustic inverse-square
  propagation. The local abstractions above preserve those physical roles
  without assuming the requested answer.
- The requested `.archon/AGENTS.md` is absent in this checkout. The available
  `.archon/prover-modes/physics-formalize.md` and the task instructions were
  followed as the role specification.
- The `archon` executable was not available on `PATH`, so the optional
  read-only DAG node/ancestor query could not be completed.
- The blueprint chapter exists, but it was not edited to add `\leanok` because
  the task's explicit write permissions allow edits only to the assigned Lean
  file and this result file. The plan/controller agent should add `\leanok` to
  `thm:physics:phyx_mini_0216:target`.

## Verification

- Lean language-server diagnostics report exactly three expected
  `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0216.lean` exits with code
  0 and the same three expected warnings.
