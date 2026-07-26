# Post-formalization result: `problem_phyx_mini_0287.lean`

This report was regenerated after auditing the final Lean model, the source
report, and the primary image for Archon iteration 002. It addresses the review
gate's missing-evidence reason.

## Assumption/target split

### Governing laws and physical admissibility

- `MatchesTravelingStringWaveScenario` says that the wave is sinusoidal and
  traveling and that its string tension has positive newton readout.
- `HasPhysicalStringWaveParameters` gives positivity/nondegeneracy of the
  amplitude, wavelength, angular frequency, wave number, and maximum slope
  magnitude. It does not assign the requested amplitude a numerical value.
- `SatisfiesSinusoidalTravelingWaveLaws` gives the general relations
  `k * lambda = 2 * pi` and `S_max = k * A`, the sinusoidal traveling-wave
  displacement profile, the `HasDerivAt` relation between displacement and
  spatial slope, and a bound by the maximum slope magnitude.

### Previous-part results

- None. `reports/phyx_mini/problem_phyx_mini_0287.source.json` has an empty
  `previous_parts` array.

### Figure/data readouts

- `SlopeGraphFigure1631` keeps the physical `x_s` length, meter coordinates,
  dimensionless `dy/dx` readouts, and the visible axis/scale/grid labels
  separate from the modeled wave.
- `MatchesSlopeGraphFigure1631` records `x_s = 0.80 m`, positive slope crests
  at `0`, `0.40 m`, and `0.80 m`, negative troughs at `0.20 m` and `0.60 m`,
  and alternating readouts `+0.20` and `-0.20`. Direct inspection of
  `phyx_data/test_image/287.png` confirms these five extrema and labels.
- The figure interpretation identifies wavelength with adjacent positive-crest
  spacing and maximum slope magnitude with the positive crest readout.
- `displayedAmplitudeInMeters` records all four printed choices.
  `recordedDatasetAnswer` preserves the dataset's D label as metadata; it is
  not a theorem premise.

### Current target conclusions

- `lengthInMeters setup.amplitude = (1 / 25) / Real.pi`.
- The exact value rounds to the displayed `0.0127 m` for the recorded choice D.
- D is the unique displayed choice within half of `0.0001 m` of the exact
  amplitude.

## Source/law/answer audit

The primary image gives `lambda = 0.40 m` from the separation between adjacent
positive slope crests and `S_max = 0.20` from the vertical extremum. The generic
laws yield `k = 2 pi / lambda` and `S_max = k A`, hence
`A = S_max * lambda / (2 pi) = 1 / (25 pi) m`, approximately `0.012732 m`.
Thus the physical derivation supports the recorded answer D (`0.0127 m`) after
rounding; there is no source/law/answer conflict.

## Goal-faithfulness audit

`SinusoidalStringWaveSetup.amplitude` is an independent dimensionful quantity.
No premise field states its exact value, its displayed value, the D choice, or
the rounding/uniqueness conclusions. The law `S_max = k * A` is a general
sinusoidal-wave law with no figure-specific number, while the figure predicate
contains only calibrated readouts and their physical interpretation. The
target therefore still requires combining independent wave laws with image
evidence.

`recordedDatasetAnswer := .D` only names source metadata. Unfolding it cannot
establish the exact amplitude, the rounding inequality, or uniqueness among
the four choices. Likewise, `RoundsToDisplayedFourDecimalMeters` merely defines
the usual half-unit rounding interval and does not assert that it holds.

## Declarations and blueprint correspondence

- Unit layer: `LengthQuantity`, `TensionQuantity`,
  `AngularFrequencyQuantity`, `lengthReadout`, `tensionReadout`,
  `angularFrequencyReadout`, `lengthInMeters`, `tensionInNewtons`, and
  `angularFrequencyInRadiansPerSecond`.
- Scenario/figure labels: `StringWaveKind`, `PropagationDirection`,
  `propagationDirectionSign`, `SlopeGraphExtremum`, `SlopeExtremumKind`, and
  `extremumKind`.
- Physical and image models: `SlopeGraphFigure1631`,
  `SinusoidalStringWaveSetup`, `MatchesTravelingStringWaveScenario`,
  `HasPhysicalStringWaveParameters`, `SatisfiesSinusoidalTravelingWaveLaws`,
  and `MatchesSlopeGraphFigure1631`.
- Answer model: `AnswerChoice`, `displayedAmplitudeInMeters`,
  `recordedDatasetAnswer`, `RoundsToDisplayedFourDecimalMeters`, and
  `IsUniqueMatchingAnswerChoice`.
- `problem_phyx_mini_0287` corresponds to
  `thm:physics:phyx_mini_0287:target`. The chapter has no additional Lean
  declaration labels.

These support declarations are all public because the chapter's model must be
available to the later prover; none has a theorem proof body. The sole theorem
body is the stage-required `by sorry`.

## LeanExplore queries and candidates actually checked

All searches used `packages: ["Mathlib", "Physlib"]`.

- `one-dimensional transverse sinusoidal traveling string wave displacement
  slope amplitude wavelength` returned
  `ClassicalMechanics.transverseHarmonicPlaneWave`,
  `ClassicalMechanics.harmonicWave`, and `ClassicalMechanics.WaveEquation`.
  Source/module/docstring were fetched for
  `ClassicalMechanics.transverseHarmonicPlaneWave` (declaration 385509).
- `Dimensionful WithDim physical quantity units` returned `Dimensionful`,
  `CarriesDimension.toDimensionful`, `HasDimension`, and related scaling
  declarations. Source/module/docstring were fetched for `Dimensionful`
  (394284) and, after the exact-name query `WithDim`, for `WithDim` (394425).
- `Real.hasDerivAt_sin` returned that exact theorem plus `Real.deriv_sin` and
  `Real.hasDerivAt_cos`. Source/module/docstring were fetched for
  `Real.hasDerivAt_sin` (147274).
- `HasDerivAt` returned the core predicate and `HasDerivAt.sin`; details were
  fetched for `HasDerivAt` (124761).
- `LengthUnit.meters UnitChoices.SI MassUnit.kilograms TimeUnit.seconds` and the
  exact-name follow-ups grounded `UnitChoices.SI`, `LengthUnit`,
  `MassUnit.kilograms`, and `TimeUnit.seconds`. Source/module/docstring were
  fetched for declarations 394270, 393137, 385377, and 393630 respectively.
  LeanExplore did not rank `LengthUnit.meters` itself, so its exact type and
  import were additionally confirmed by LSP hover in the completed file.

## Physlib/Mathlib names grounded and used

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.M𝓭`,
  `Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.meters`,
  `MassUnit.kilograms`, and `TimeUnit.seconds`.
- Mathlib: `NNReal`, `Real.sin`, `Real.pi`, and `HasDerivAt`.
- `Real.hasDerivAt_sin` was grounded as an appropriate later proof tool for the
  derivative law, although this autoformalization stage only places
  `HasDerivAt` in the statement.

## Local abstractions introduced

- `SinusoidalStringWaveSetup` is a scalar-transverse, one-dimensional string
  model with dimensionful amplitude, wavelength, tension, and angular
  frequency, plus explicitly named coherent-SI scalar readouts.
- `SlopeGraphFigure1631` and `MatchesSlopeGraphFigure1631` preserve the primary
  image's labels, geometry, and dimensionless slope data independently of the
  requested answer.
- Separate scenario, admissibility, governing-law, and figure predicates make
  the source/law/target boundary explicit.
- `RoundsToDisplayedFourDecimalMeters` separates the exact physical amplitude
  from the decimal values printed in the multiple-choice answers.

## Grounding gaps and redraft requests

- The closest Physlib wave object,
  `ClassicalMechanics.transverseHarmonicPlaneWave`, is a three-dimensional
  Euclidean plane wave with real component amplitudes. It does not model a
  one-dimensional string, dimensionful string amplitude, or the plotted
  dimensionless spatial-slope graph. The local setup is therefore the smallest
  faithful specialization needed here.
- `.archon/AGENTS.md` is absent. The explicit assignment,
  `.archon/PROGRESS.md`, and `.archon/prover-modes/physics-formalize.md` were
  followed instead.
- The `archon` executable is not on `PATH`, so the optional read-only DAG query
  could not run. The chapter exposes only the single target label and names no
  dependencies.
- The blueprint contains `% archon:physics` and already supplies the formalize
  target, but the assignment permits edits only to the Lean file and this
  report. A coordinator with blueprint write permission should add `\\leanok`
  to `thm:physics:phyx_mini_0287:target` after acceptance.
- No statement redraft is requested. No `/- USER: ... -/` hints occur in the
  assigned Lean file.

## Verification

- `archon-lean-lsp` reports no errors and exactly one expected warning:
  `problem_phyx_mini_0287` uses `sorry`.
- The model imports Mathlib and compiles in the project Lake environment.
