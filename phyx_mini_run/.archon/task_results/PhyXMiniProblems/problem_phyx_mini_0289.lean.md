# Autoformalization result: `problem_phyx_mini_0289.lean`

## Assumption/target split

### Governing laws

- `SatisfiesTravelingSinusoidalWaveLaws.crestTranslationKinematics` states
  `d = v Δt` in every coherent choice of length and time units.
- `SatisfiesTravelingSinusoidalWaveLaws.waveNumberWavelengthRelation` states
  `k λ = 2π` using SI readouts.
- `SatisfiesTravelingSinusoidalWaveLaws.angularFrequencyWaveSpeedRelation`
  states the general traveling-wave relation `ω = k v`.
- `SatisfiesTravelingSinusoidalWaveLaws.positiveXSinusoidalWaveform` states
  `y(x,t) = y_m sin(kx - ωt)` for the scalar SI displacement component.  The
  minus sign is the sign appropriate to propagation in positive `x`.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records `d = 6 cm`, `Δt = 4 ms`, horizontal
  tick spacing `10 cm`, and peak-to-trough height `H = 6 mm`.
- The primary image, rather than the auxiliary caption, shows `H` extending
  from the positive crest level to the negative trough level.  Accordingly,
  `heightIsPeakToTrough` records `H = 2 y_m` rather than treating `H` itself as
  the amplitude.
- The solid curve is the earlier snapshot, the dashed curve is later, the
  coordinate axes carry labels `x` and `y`, and the labels `A`, `d`, and `H`
  are assigned to their distinct figure roles.
- Crest `A` moves in positive `x` by `d`; its earlier depicted position is at
  the fifth 10 cm tick, and one wavelength spans four tick intervals.
- The earlier snapshot is chosen as the time origin. This is a coordinate
  convention, while the two snapshot times remain separated by the physical
  elapsed duration.
- `HasPhysicalWaveParameters` states positivity/nondegeneracy only; it does
  not assign a numerical value to the requested angular frequency.

### Current target conclusions

- The exact angular-frequency readout is `75 * Real.pi` radians per second.
- This exact value lies within the half-width for rounding to the nearest ten
  of `240 rad/s`, so it matches displayed answer D (`2.4 × 10^2 rad/s`).

## Goal-faithfulness audit

The exact expression `75 * Real.pi` and the nearest-ten agreement with choice
D occur only in the conclusion of `problem_phyx_mini_0289`. They are absent
from `TravelingStringWaveExperiment`, `MatchesProblemAndPrimaryFigure`,
`HasPhysicalWaveParameters`, and `SatisfiesTravelingSinusoidalWaveLaws`.
The experiment stores angular frequency as an independent unit-aware physical
quantity rather than defining it to be the answer.

The governing-law interface stops at the general relations `d = v Δt`,
`k λ = 2π`, and `ω = k v`; deriving the speed, wavelength, wave number, and
final angular frequency remains a proof obligation.  Choice D's `240` is only
the answer-choice display data, and `MatchesNearestTenDisplay` is a genuine
numerical inequality, not an exact equality hidden in a definition.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0289:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0289.problem_phyx_mini_0289`.
- Dimensionful roles: `LengthQuantity`, `TimeQuantity`, `SpeedQuantity`,
  `WaveNumberQuantity`, and `AngularFrequencyQuantity`.
- Unit projections: `lengthReadout`, `timeReadout`, `speedReadout`,
  `waveNumberInRadiansPerMeter`, and
  `angularFrequencyInRadiansPerSecond`.
- Figure/setup model: `Snapshot`, `CurveStyle`, `Axis`, `AxisLabel`,
  `FigureRole`, `FigureLabel`, `PropagationDirection`, and
  `TravelingStringWaveExperiment`.
- Assumption interfaces: `MatchesProblemAndPrimaryFigure`,
  `HasPhysicalWaveParameters`, and
  `SatisfiesTravelingSinusoidalWaveLaws`.
- Answer semantics: `AnswerChoice`, `AnswerChoice.radiansPerSecond`,
  `recordedAnswerChoice`, and `MatchesNearestTenDisplay`.

## LeanExplore queries and candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Natural-language query `dimensionful physical quantity SI units length time angular frequency`
  and name query `Dimensionful WithDim UnitChoices` found `Dimensionful`,
  `UnitChoices.SI`, `Dimension`, and
  `CarriesDimension.toDimensionful`. The formalization uses the first three.
- Name query `DimSpeed` found and grounded Physlib's unit-independent speed
  type `DimSpeed`.
- Natural-language query `sine traveling wave angular frequency wavelength speed`
  found `ClassicalMechanics.harmonicWave` and
  `ClassicalMechanics.planeWave`. These were inspected but not used: the former
  is a raw-real, cosine-based general harmonic-wave construction and the latter
  is a vector-valued plane wave with raw-real speed. Neither directly models a
  unit-aware transverse string displacement with the problem's sine phase.
- Name queries `Real.sin` and `Real.pi` grounded the Mathlib definitions used
  for the waveform and exact target.
- Query `LengthUnit.centimeters TimeUnit.milliseconds` grounded
  `LengthUnit.centimeters` and `TimeUnit.milliseconds`; the corresponding
  Physlib unit families also supply meters, millimeters, and seconds used in
  the file.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `UnitChoices.SI`, `DimSpeed`, `LengthUnit.meters`,
  `LengthUnit.centimeters`, `LengthUnit.millimeters`, `TimeUnit.seconds`, and
  `TimeUnit.milliseconds`.
- Mathlib: `NNReal`, `Real.sin`, `Real.pi`, and real absolute value notation.

## Local abstractions introduced

- The figure enums preserve the two line styles, axis labels, label roles,
  tracked crest, and propagation direction without reducing them to unrelated
  booleans or scalars.
- `TravelingStringWaveExperiment` keeps every basic physical magnitude
  unit-aware. Its real-valued displacement field is explicitly an SI scalar
  component readout, which is appropriate for the displayed formula.
- `SatisfiesTravelingSinusoidalWaveLaws` is local because the closest Physlib
  harmonic/plane-wave constructions do not combine a one-dimensional string
  model, the sine convention, and dimensionful parameters needed here. The
  local interface states standard component laws and does not contain their
  problem-specific numerical consequence.
- `MatchesNearestTenDisplay` models the answer's two-significant-figure
  rounding instead of asserting the physically false exact equality
  `75π = 240`.

## Prover result — Archon iteration 015

- Closed `PhyXMiniProblems.ProblemPhyXMini0289.problem_phyx_mini_0289`
  without changing its signature.
- Used `Dimensionful` covariance to convert the readouts to
  `d = 3/50 m`, `Δt = 1/250 s`, and tick spacing `1/10 m`.
- The supplied laws then give `v = 15 m/s`, `λ = 2/5 m`,
  `k = 5π rad/m`, and finally `ω = 75π rad/s`.
- Proved the nearest-ten display independently. Since only the basic
  trigonometric import is available, the proof obtains the sufficient bounds
  `47/15 < π < 49/15` from the imported complex-exponential remainder estimate
  and cosine monotonicity.

## Completion status

- No `sorry`, `admit`, `axiom`, `sorryAx`, `native_decide`, unsafe
  declaration, or metaprogramming escape hatch remains in the assigned file.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0289.lean` exits 0.
- The root `lake build` completes successfully.
- `lean_verify` reports no suspicious source patterns; the theorem depends
  only on the standard foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- No redraft is needed.
- Blueprint theorem `thm:physics:phyx_mini_0289:target` is ready for
  `\leanok`. Per prover permissions, the blueprint was not edited; the
  deterministic sync/review stage should apply the marker.

## Environment note

- Run-local `.archon/AGENTS.md` is absent as documented in `PROGRESS.md`; the
  identical canonical archived `AGENTS.md` was read instead.
- A named per-module Lake target is not registered for this standalone problem
  file, so the file was checked directly with `lake env lean`; the configured
  root target was also built successfully.
