# Autoformalization result: `problem_phyx_mini_0296.lean`

## Assumption/target split

### Governing laws

- `SatisfiesSinusoidalStandingWaveLaws` states the generic standing-wave model
  `y(x,t) = y_m cos(k (x-x_A)) sin(omega t + phi)` and its transverse-velocity
  law.
- The same interface states `k lambda = 2 pi`, `omega T = 2 pi`, and that the
  distance from the named antinode to the adjacent node is one quarter of a
  wavelength.
- `HasPhysicalStandingWaveParameters` supplies positivity of amplitude,
  wavelength, period, wave number, and angular frequency, together with the
  principal phase range `0 <= phi < 2 pi`.

### Previous-part results

- None.  The source report lists no previous parts.

### Figure/data readouts

- `MatchesStandingWaveProblemData` records a transverse standing wave, an
  antinode at `x = 0 m`, the adjacent node at `x = 0.10 m`, and the requested
  event `x = 0.20 m`, `t = 1.0 s`.
- `MatchesPrimaryDisplacementGraph` records the axes `t (s)` and `y (cm)`, the
  scale `y_s = 4.0 cm`, four half-second grid intervals, and the plotted
  landmarks `(0,0)`, `(0.5,-y_s)`, `(1.0,0)`, `(1.5,y_s)`, `(2.0,0)`.
- It also records the visible slope directions at the origin and at the
  `1.0 s` zero crossing.  These are observations at the graph antinode, not a
  numerical velocity at the queried `x = 0.20 m` point.
- The primary bitmap was used instead of the inconsistent auxiliary caption:
  the bitmap has its trough at `0.5 s`, rising zero at `1.0 s`, and crest at
  `1.5 s`.

### Current target conclusions

- The exact model velocity at the requested event is `-Real.pi / 25 m/s`.
- This value lies within half of `0.01 m/s` of `-0.13 m/s`, the displayed
  choice D.
- Choice D is at least as close to the exact value as every other displayed
  answer choice.

## Goal-faithfulness audit

The exact velocity `-Real.pi / 25` and the numerical choice-D value
`-13 / 100` do not occur in `MatchesStandingWaveProblemData`,
`MatchesPrimaryDisplacementGraph`, `HasPhysicalStandingWaveParameters`, or
`SatisfiesSinusoidalStandingWaveLaws`.  The former appears only in the
conclusions of `transverseVelocityAtRequestedEvent_exact` and the main
theorem.  The latter is one branch of the answer-choice readout function and
is selected only in the target through the independently recorded answer
label.  No premise asserts the requested velocity, its rounding, or that D is
closest.  No local definition unfolds the physical target into a reflexive
equality.

The slope hypotheses describe the graph at `x = 0`; the target concerns the
distinct point `x = 0.20 m`.  The sign reversal at that point must be derived
from the quarter-wavelength geometry and the standing-wave spatial cosine.

## Declarations and blueprint correspondence

- Dimensionful quantities/readouts: `AmplitudeQuantity`,
  `WavelengthQuantity`, `SignedLengthQuantity`, `TimeQuantity`,
  `DurationQuantity`, `AngularFrequencyQuantity`, `WaveNumberQuantity`,
  `TransverseVelocityQuantity`, and their named-unit readout functions.
- Figure/geometry vocabulary: `SpatialLandmark`, `StandingWaveRole`,
  `GraphAxis`, `AxisQuantity`, `DisplacementGraphLandmark`, and
  `DisplacementTimeGraph`.
- Physical setup and premises: `StandingStringWaveSetup`,
  `MatchesStandingWaveProblemData`, `MatchesPrimaryDisplacementGraph`,
  `HasPhysicalStandingWaveParameters`, and
  `SatisfiesSinusoidalStandingWaveLaws`.
- Derived helper statements: `wavelengthInMeters_eq_two_fifths`,
  `waveNumberInRadiansPerMeter_eq_five_pi`,
  `angularFrequencyInRadiansPerSecond_eq_pi`,
  `phaseOffsetRadians_eq_pi`, `requestedPointSpatialPhase_eq_pi`, and
  `transverseVelocityAtRequestedEvent_exact`.
- Answer vocabulary: `AnswerChoice`,
  `displayedVelocityInMetersPerSecond`, `recordedDatasetAnswer`, and
  `MatchesDisplayedVelocity`.
- `problem_phyx_mini_0296` corresponds to
  `thm:physics:phyx_mini_0296:target`.

## LeanExplore grounding

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `transverse standing wave string displacement antinode node`
- `standing wave`
- `Dimensionful WithDim length time speed LengthUnit TimeUnit`
- `derivative sine cosine chain rule`
- `WithDim`
- `TimeUnit`
- `UnitChoices`
- `Real.sin Real.cos Real.pi`

Candidates inspected through LeanExplore source/module/docstring lookups:

- `Dimensionful` from `Physlib.Units.Basic`: used for all physical quantities.
- `WithDim` from `Physlib.Units.WithDim.Basic`: used to attach the length,
  time, inverse-time, inverse-length, and speed dimensions to scalar carriers.
- `LengthUnit` from `Physlib.SpaceAndTime.Space.LengthUnit`, `TimeUnit` from
  `Physlib.SpaceAndTime.Time.TimeUnit`, and `UnitChoices` from
  `Physlib.Units.Basic`: used by the coherent named-unit readout functions.
- `Dimension.L𝓭` from `Physlib.Units.Dimension`: used as the length
  dimension (with `Dimension.T𝓭` checked locally for time).
- `Real.sin` from `Mathlib.Analysis.Complex.Trigonometric`: used in the
  displacement law; `Real.cos` and `Real.pi` were also checked under the
  selected imports.
- `HasDerivAt.sin` from
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`: its sine chain-rule
  form grounds the scalar factor in the local dimensionful transverse-velocity
  law.
- `ClassicalMechanics.transverseHarmonicPlaneWave` from
  `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave`: not used because it
  constructs a three-dimensional traveling plane wave with two transverse
  polarizations, not a one-dimensional standing wave on a string.

Local LSP search found `Dimensionful` and `WithDim` in the installed Physlib.
A compiling LSP snippet additionally verified `Dimension.L𝓭`,
`Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit.meters`,
`LengthUnit.centimeters`, `TimeUnit.seconds`, `Real.sin`, `Real.cos`, and
`Real.pi` under the selected imports.  Local search did not index the unit
constructor names, so the compiling snippet was used as the authoritative
availability check for them.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit.meters`,
  `LengthUnit.centimeters`, and `TimeUnit.seconds`.
- Mathlib: `NNReal`, `Real.sin`, `Real.cos`, `Real.pi`, and real absolute-value
  notation.

## Local abstractions introduced

Physlib has no matching one-dimensional standing-string-wave object.  The
local setup and law structures keep displacement, wavelength, time, angular
frequency, wave number, and velocity dimensionful while exposing only
coherent scalar readouts in named units.  The local figure structures retain
the printed axis variables, units, scale label, spatial roles, and temporal
landmarks.  `MatchesDisplayedVelocity` is a general nearest-hundredth
tolerance predicate rather than a definition specialized to choice D.

## Grounding gaps and redraft requests

- No suitable Physlib standing-wave-on-a-string API was found; the closest
  plane-wave candidate has the dimensional/physical mismatch described above.
- The optional `archon dag-query` navigation command was unavailable in this
  shell (`archon: command not found`); the blueprint and source report list no
  previous-part dependencies, so this did not weaken the formalization.
- `.archon/AGENTS.md` was absent in this checkout.  The complete available
  `.archon/prover-modes/physics-formalize.md` role file was followed instead.
- The blueprint theorem environment was not edited to add `\leanok` because
  this task's explicit write-permission block allows changes only to the
  assigned Lean file and this result file and expressly forbids blueprint
  edits.  The plan/controller agent should add `\leanok` to
  `thm:physics:phyx_mini_0296:target`.

## Verification

`archon-lean-lsp` diagnostics report successful elaboration with only the seven
expected `declaration uses sorry` warnings.  The final command
`lake env lean PhyXMiniProblems/problem_phyx_mini_0296.lean` also exits with
status 0 and exactly those seven warnings.
