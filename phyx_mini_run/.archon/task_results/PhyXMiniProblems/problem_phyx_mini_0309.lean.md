# Autoformalization result: `problem_phyx_mini_0309.lean`

## Assumption/target split

### Governing laws

- The longitudinal displacement has the stated normal form
  `s(x,t) = s_m cos(kx - ωt)`.
- The pressure monitor sees the quadrature sinusoidal pressure change at its
  fixed position.
- Cyclic frequency and period obey `f T = 1`.
- Angular and cyclic frequencies obey `ω = 2 π f`.
- The nondispersive sound-wave phase-speed relation is `ω = k v`.
- The plane-wave pressure amplitude obeys `Δp_m = ρ v ω s_m`.
- Positivity assumptions select a nondegenerate physical wave.

These are represented by `SatisfiesSingleFrequencyPlaneSoundWaveLaws` and
`HasPhysicalAcousticParameters`. None contains the requested closed form or a
displayed answer value.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- The medium is air, the propagation speed is `343 m/s`, and the uniform mass
  density is `1.21 kg/m³`.
- The axes are labelled `t (ms)` and `Δp (mPa)`, and the pressure scale is
  labelled `Δp_s = 4.0 mPa`.
- From the primary image, zeros occur at `-1, 0, 1, 2 ms`; positive peaks occur
  at `-0.5` and `1.5 ms`; and the trough occurs at `0.5 ms`.
- The primary image places the `±Δp_s` marks halfway between zero and the
  extrema, so the pressure peak magnitude is `2 Δp_s = 8 mPa`.
- The physical period is the time separation between the two equal positive
  peaks. The exact `2 ms` period is consequently a derived lemma, not a numeric
  premise about `k`.
- The pressure curve passes through every dimensionful marked figure value,
  and the monitor is chosen as the spatial coordinate origin.

These readouts are represented by `PressureTimeFigure` and
`MatchesProblemStatementAndFigure`.

### Current target conclusions

- Exact wave number:
  `waveNumberInRadiansPerMeter setup.waveNumber = 1000 * Real.pi / 343`.
- Nearest-tenth display agreement with recorded answer choice D, whose printed
  value is `9.2 rad/m`.

The final target is `problem_phyx_mini_0309`; its rounding clause uses a strict
half-width of `0.05 rad/m` rather than falsely identifying the exact irrational
value with the decimal `9.2`.

## Goal-faithfulness audit

The requested wave-number equality and nearest-choice assertion occur only in
derived lemma/theorem conclusions. They do not occur in
`MatchesProblemStatementAndFigure`, `HasPhysicalAcousticParameters`,
`SatisfiesSingleFrequencyPlaneSoundWaveLaws`, the setup structure, or a local
definition that unfolds to the result.

The figure premises determine a period from independent peak coordinates; the
governing laws then require deriving `f`, `ω`, and finally `k`. The answer-choice
table merely records the four printed options, and `recordedAnswerChoice := .D`
records dataset metadata. Neither fact proves `MatchesNearestTenthDisplay`; the
numerical closeness remains part of the final theorem obligation.

The pressure scale, density, and pressure-amplitude law are retained even
though they cancel out of the route to `k`. Thus the physical setup is not
reduced to only the quantities appearing in the final closed form.

## Declarations created and blueprint mapping

- Dimensionful quantities and readouts:
  `TimeQuantity`, `SignedTimeQuantity`, `LengthQuantity`,
  `SignedLengthQuantity`, `SpeedQuantity`, `PressureQuantity`,
  `MassDensityQuantity`, `FrequencyQuantity`, `AngularFrequencyQuantity`,
  `WaveNumberQuantity`, and their named-unit readout functions.
- Figure vocabulary:
  `FigureLabelRole`, `FigureLabel`, `PressureDisplayUnit`, `FigureTimeMark`,
  `PressureTimeFigure`, and `AcousticMedium`.
- Physical model and assumptions:
  `AcousticPressureMonitorSetup`, `MatchesProblemStatementAndFigure`,
  `HasPhysicalAcousticParameters`, and
  `SatisfiesSingleFrequencyPlaneSoundWaveLaws`.
- Derived lemmas:
  `wavePeriodInMilliseconds_eq_two`,
  `cyclicFrequencyInHertz_eq_fiveHundred`,
  `angularFrequencyInRadiansPerSecond_eq_oneThousand_pi`, and
  `waveNumberInRadiansPerMeter_eq_oneThousand_pi_div_343`.
- Answer representation:
  `AnswerChoice`, `AnswerChoice.radiansPerMeter`, `recordedAnswerChoice`, and
  `MatchesNearestTenthDisplay`.
- Blueprint label `thm:physics:phyx_mini_0309:target` corresponds to theorem
  `PhyXMiniProblems.ProblemPhyXMini0309.problem_phyx_mini_0309`.

The blueprint chapter was not edited because the task's explicit write
permissions forbid editing blueprint chapters. A coordinator or plan agent
should add `\leanok` to the target environment after accepting this file.

## LeanExplore queries and candidates used

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `acoustic sound pressure traveling wave wave number angular frequency speed relation`
  found `DimPressure`, `ClassicalMechanics.harmonicWave`,
  `ClassicalMechanics.planeWave`, and harmonic-oscillator declarations.
- `DimSpeed Dimensionful WithDim inverse length inverse time pressure density`
  found `Dimensionful`, `DimPressure`, `DimSpeed`, and the dimension API.
- `Real.pi absolute value nearest displayed decimal` found `Real.pi` and
  explicit pi-bound lemmas.
- `DimDensity mass density kilograms per cubic meter` found
  `FluidDynamics.MassDensity`.
- `TimeUnit.milliseconds LengthUnit.meters UnitChoices.SI` found
  `TimeUnit.milliseconds`, `LengthUnit`, and `UnitChoices.SI`.
- `Real.cos cosine real` confirmed the Mathlib real trigonometric API.

Source and module information was fetched for the candidates actually assessed
for use: `DimPressure`, `DimSpeed`, `Dimensionful`,
`FluidDynamics.MassDensity`, `ClassicalMechanics.harmonicWave`,
`TimeUnit.milliseconds`, `UnitChoices.SI`, and `Real.pi`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `Dimension.M𝓭`, `DimPressure`, `DimSpeed`, `UnitChoices.SI`, `LengthUnit`,
  `TimeUnit`, and `TimeUnit.milliseconds`.
- Mathlib: `Real.sin`, `Real.cos`, `Real.pi`, real absolute value notation, and
  `NNReal`.
- Imports were kept to
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`,
  `Physlib.Units.WithDim.Pressure`, and `Physlib.Units.WithDim.Speed`.

## Local abstractions introduced

- `MassDensityQuantity` is a unit-independent physical scalar with dimension
  `M L⁻³`. LeanExplore's `FluidDynamics.MassDensity d` is a generic scalar
  field alias and does not itself preserve a dimensionful uniform density
  readout, so it was not a faithful replacement for the stated `1.21 kg/m³`.
- Inverse-time frequency/angular-frequency and inverse-length wave-number
  quantities use Physlib `Dimensionful (WithDim ... NNReal)` directly because
  no dedicated acoustic wrappers were found.
- The figure/setup/law structures are the smallest local interfaces that retain
  the labelled graph, signed pressure signal, acoustic medium, and standard
  sound-wave relations. They are not scalar aliases for physical primitives.
- `MatchesNearestTenthDisplay` models the precision of the printed choices
  without building the selected answer into the physical laws.

## Grounding gaps

- No dedicated Physlib acoustic plane-wave API or theorem for `ω = kv` and
  `Δp_m = ρvωs_m` was found. `ClassicalMechanics.harmonicWave` is a general
  scalar function on `Time → Space d`; its amplitude and phase are not the
  dimensionful acoustic quantities required here. The local governing-law
  interface therefore states these physical laws explicitly.
- The requested `.archon/AGENTS.md` file does not exist in this checkout. The
  stage-specific `.archon/prover-modes/physics-formalize.md` role document was
  read and followed instead.
- The `archon` executable was not available on `PATH`, so the optional DAG
  queries could not be run. The chapter contains no declared dependency labels
  besides its own target.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0309.lean` exits successfully.
The only diagnostics are the five expected `declaration uses sorry` warnings
for the four derived lemmas and the final theorem.
