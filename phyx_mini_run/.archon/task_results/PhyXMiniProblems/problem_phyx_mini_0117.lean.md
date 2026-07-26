# Autoformalization result: `problem_phyx_mini_0117.lean`

## Assumption/target split

### Governing laws

- `SatisfiesFreeSpaceTwoSourceLaws` states the unit-consistent vacuum dispersion relation
  `c = f * wavelength` using SI scalar readouts.
- The same predicate states, uniformly for both antennas and every nonnegative receiver
  distance, that each ray-path length is the Euclidean distance from the corresponding
  antenna to the receiver.
- Conditional on the separately supplied in-phase emission premise, the same predicate
  states the general destructive-interference criterion
  `2 * pathDifference = (2 * order + 1) * wavelength` for an arbitrary natural order and
  arbitrary nonnegative receiver distance.
- `RadiatesInPhaseAtCommonFrequency` says that antennas A and B emit with equal source
  phase and both use the stated common radio frequency.
- `HasPhysicalParameters` supplies positivity of separation, frequency, wavelength, and
  propagation speed, together with nonnegativity of candidate distances and ray lengths.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `HasDepictedGeometry` records B at the origin, A vertically above B, C on the positive
  horizontal axis, and a receiver at distance `x` from B at metre coordinates `(x, 0)`.
  These coordinates encode `AB perpendicular BC` from the primary image.
- The physical A--B separation is `200 m`.
- The common frequency is `5.80 MHz`.
- Propagation speed is Physlib's dimensionful `DimSpeed.speedOfLight`.
- The displayed answer distances are A = `200 m`, B = `250 m`, C = `275 m`, and
  D = `225 m`.

### Current target conclusions

- `problem_phyx_mini_0117` concludes that the physical distance displayed as choice A is
  a location of destructive interference, matching the dataset's recorded answer
  “A: 200m.”
- `wavelength_meters_eq_speed_div_frequency` and `pathDifferenceMeters_eq` are
  conclusion-side intermediate lemmas. They derive, respectively, the dispersion-law
  wavelength and the right-triangle path-difference formula; neither is assumed by the
  main theorem.

## Goal-faithfulness audit

No premise says that choice A, `200 m`, or any displayed answer is destructive. The
answer-table premise gives only metre readouts. `destructiveInterferenceAt` is an abstract
observable indexed by every physical receiver distance; the setup contains no proof that
it holds anywhere. The governing-law predicate constrains that observable only through a
uniform odd-half-wavelength equivalence for every nonnegative distance and never mentions
an answer label or displayed numerical distance. Consequently, reaching the theorem's
choice-A conclusion still requires applying the physical laws, deriving the wavelength
and ray lengths, and completing substantive numerical reasoning.

The helper definitions `metersValue`, `hertzValue`, `megahertzValue`, and
`metersPerSecondValue` are named unit projections from Physlib dimensionful quantities.
They do not define an unknown distance, path difference, or interference result to be the
target value.

## Declarations created and blueprint correspondence

- Physical types and readouts: `LengthQuantity`, `FrequencyQuantity`, `SpeedQuantity`,
  `metersValue`, `hertzValue`, `megahertzValue`, `metersPerSecondValue`.
- Figure/source/answer labels: `FigurePoint`, `AntennaLabel`,
  `AntennaLabel.figurePoint`, `AnswerChoice`, `displayedDistanceMeters`.
- Physical objects: `RadioAntenna`, `TwoAntennaInterferenceSetup`.
- Premise predicates: `RadiatesInPhaseAtCommonFrequency`, `HasDepictedGeometry`,
  `HasStatedReadouts`, `HasPhysicalParameters`, `SatisfiesFreeSpaceTwoSourceLaws`.
- Derived quantity: `pathDifferenceMeters`.
- Derived lemmas: `wavelength_meters_eq_speed_div_frequency`,
  `pathDifferenceMeters_eq`.
- Target theorem: `problem_phyx_mini_0117`, corresponding to
  `thm:physics:phyx_mini_0117:target`.

The blueprint chapter was not edited because the task's explicit write permissions allow
changes only to the assigned Lean file and this task-result file.

## LeanExplore queries/candidates actually used

- Natural-language query: `two coherent in-phase point sources destructive interference
  path difference half integer wavelength` with packages `Mathlib`, `Physlib`.
  Results were unrelated topological `Path` declarations and harmonic-function results;
  no point-source interference law was found.
- Likely-name query: `destructiveInterference pathDifference wavelength wave frequency
  speedOfLight` with packages `Mathlib`, `Physlib`. This found
  `ClassicalMechanics.planeWave`, `ClassicalMechanics.WaveEquation`,
  `Electromagnetism.FreeSpace.c`, and `SpeedOfLight`.
- Dimensional query: `Dimensionful WithDim length inverse time frequency UnitChoices
  LengthUnit TimeUnit` with packages `Mathlib`, `Physlib`. This found `Dimensionful`,
  `Dimension.L𝓭`, and the directly useful dimensionful constant
  `DimSpeed.speedOfLight`.
- Geometry query: `Space Euclidean distance finite dimensional real coordinates Physlib`
  with packages `Mathlib`, `Physlib`. This found `Space.dist_eq` and the Euclidean metric
  instances for `Space`.
- Source/module/docstring were fetched for `Electromagnetism.FreeSpace.c`, `SpeedOfLight`,
  `DimSpeed.speedOfLight`, `Dimensionful`, and `Space.dist_eq` before selecting the APIs.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`,
  `TimeUnit.microseconds`, `DimSpeed.speedOfLight`, and `Space 2` with its Euclidean
  `dist` instance.
- Mathlib: `Real.Angle`, `Real.sqrt`, real absolute value notation, and `dist`.
- `archon-lean-lsp` successfully checked a standalone snippet containing the three
  dimensionful quantity types, MHz/SI readout functions, `DimSpeed.speedOfLight`,
  `Space.dist_eq`, `dist`, and `Real.sqrt` before the file was written.

`Electromagnetism.FreeSpace.c : SpeedOfLight` was inspected but not used: its
`SpeedOfLight.val` is documented as a scalar in an arbitrary chosen system of units and
does not provide the needed typed bridge among dimensionful SI length, inverse time, and
speed. `DimSpeed.speedOfLight` has exactly the required
`Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)` type and is defined as `299792458 m/s`.

## Local abstractions introduced

- `RadioAntenna` keeps emission frequency and angular phase as distinct physical roles.
- `TwoAntennaInterferenceSetup` retains labeled figure geometry, dimensionful separation,
  wavelength, frequency, speed, receiver distance, ray lengths, displayed physical
  distances, and the destructive-interference observable.
- `SatisfiesFreeSpaceTwoSourceLaws` is the smallest local governing-law interface needed
  because no Mathlib/Physlib radial two-source interference declaration was found.
- The three quantity abbreviations are aliases of Physlib's unit-aware `Dimensionful`
  construction, not scalar aliases or one-field scalar wrappers.

## Grounding gaps

- LeanExplore exposed plane-wave and wave-equation APIs, but these do not model radial
  propagation from two point antennas or an odd-half-wavelength destructive-interference
  condition. The faithful local law interface fills that gap.
- No ready-made Physlib frequency alias was found; inverse-time dimension
  `Dimensionful (WithDim T𝓭⁻¹ ℝ)` was therefore used directly.

## Redraft request: recorded answer appears physically inconsistent

Using the grounded Physlib value `c = 299792458 m/s` and `f = 5.80 MHz` gives
`wavelength approximately 51.6884 m`. Along the depicted ray, the path difference at
distance `x` from B is `sqrt(200^2 + x^2) - x`.

- At recorded choice A (`x = 200 m`), the path difference is approximately `82.8427 m`,
  or `1.60273` wavelengths, not an odd half-integer number of wavelengths.
- At choice D (`x = 225 m`), it is approximately `1.47112` wavelengths, the closest
  displayed candidate to the `3/2`-wavelength destructive condition.
- Solving the exact `3 wavelength / 2` condition gives approximately `219.190 m`.

Thus the faithfully modeled target theorem is not derivable from the stated exact data;
its `sorry` is expected to remain until the source answer is corrected or the intended
approximation/selection rule is clarified. The likely multiple-choice answer is D
(`225 m`), not the recorded A (`200 m`).

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0117.lean` succeeds with exactly the
three expected warnings for the `sorry` bodies and no errors.
