# Autoformalization result: `problem_phyx_mini_0223.lean`

## Iteration-003 retry-gate remediation

The exact iteration-002 review reason was:

> No genuine post-formalization task result exists for retry target 0223. The only current evidence is the generic physics-grounding preflight, which predates the revised Lean model and cannot establish the queries/candidates actually used, grounded Mathlib/Physlib names, introduced local abstractions, grounding gaps, or source/law/answer split; missing evidence is a failed review.

This report was regenerated after the current Lean file was reviewed against
the current source report, blueprint chapter, and primary image; the searches
listed below were actually rerun against Mathlib and Physlib; the four selected
library declarations were inspected by source and module; and the assigned file
was compiled in the real Lake environment. The physical model and theorem
signatures were retained because this audit found no semantic defect.

The current file directly imports `Mathlib` and
`Physlib.Units.WithDim.Speed`. The source report records no previous parts. The
primary image confirms that the `0.395 m` arrow runs from the tube opening to
the dashed lower water-level mark, while the `0.125 m` arrow runs from the same
opening to the solid upper water level.

## Assumption/target split

### Governing laws

- The upper end open to the atmosphere is a displacement antinode.
- The lower boundary at the water surface is a displacement node.
- For each observed closed-open resonance, measured air-column length plus a common opening-end correction equals `(2 n + 1) λ / 4`.
- Acoustic propagation obeys `v = f λ` in coherent SI readouts.
- Physical frequency, wavelength, and propagation speed have positive SI readouts.
- The standard room-condition sound-speed calibration is `343 m/s`. This is kept in the separate predicate `HasStandardAirSoundSpeed`, rather than being presented as a datum printed in the problem.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- The first, solid-marked water level gives an air-column length of `0.125 m = 1/8 m`.
- The second, dashed lower water level gives an air-column length of `0.395 m = 79/200 m`.
- The wording that resonance is heard and then heard "again" as the level falls slowly is represented by consecutive mode indices.
- The tube is vertical, its upper boundary is open to the atmosphere, its lower air-column boundary is the water surface, and the fork is above the opening.
- The primary image was used to resolve the auxiliary caption: `0.395 m` is the top-to-dashed-level second resonant air-column length, not the total height of liquid.

### Current target conclusions

- Intermediate derived conclusions: successive-resonance spacing is `λ/2`, the wavelength is `27/50 m = 0.540 m`, and the exact modeled frequency is `17150/27 Hz`.
- Final conclusion: the modeled frequency lies within `1/2 Hz` of the displayed `635 Hz`, hence matches recorded answer choice D.

## Goal-faithfulness audit

Neither `635`, choice D, nor `17150/27` occurs in `TuningForkTubeSetup`, `MatchesProblemAndFigureData`, `HasStandardAirSoundSpeed`, `HasPhysicalWaveParameters`, or `SatisfiesClosedOpenAirColumnLaws`. The answer values occur only in the displayed-answer map and on conclusion sides. `MatchesAnswerChoice` gives the ordinary nearest-whole-hertz semantics and does not make the theorem true by unfolding.

The hypotheses contain only measured geometry, a standard sound-speed calibration, positivity, the consecutive-mode interpretation, and general acoustic laws. A single end-correction quantity is used in both resonance equations. This avoids the inconsistent idealization that would simultaneously identify `0.125 m` with an exact quarter wavelength and infer `λ = 0.540 m` from the spacing. For example, first mode index `0`, wavelength `0.540 m`, and end correction `0.010 m` satisfy both displayed effective-length equations, so the model is not vacuous.

The exact physical-model output is `17150/27 ≈ 635.185 Hz`; the final statement uses a half-hertz rounding interval instead of asserting the false exact equality `17150/27 = 635`.

## Declarations created and blueprint correspondence

For compactness, the definition-label prefix below is
`def:physics:phyx-mini-0223:phyxminiproblems-problemphyxmini0223-`.

- Dimensionful quantities/readouts: `LengthQuantity` → `...-lengthquantity`,
  `FrequencyQuantity` → `...-frequencyquantity`, `SpeedQuantity` →
  `...-speedquantity`, `lengthInMeters` → `...-lengthinmeters`,
  `frequencyInHertz` → `...-frequencyinhertz`, and
  `speedInMetersPerSecond` → `...-speedinmeterspersecond`.
- Geometry/model types: `ResonanceObservation` → `...-resonanceobservation`,
  `AirColumnBoundary` → `...-aircolumnboundary`, `BoundaryKind` →
  `...-boundarykind`, `DisplacementBoundaryBehavior` →
  `...-displacementboundarybehavior`, `TubeOrientation` →
  `...-tubeorientation`, `ForkPosition` → `...-forkposition`,
  `WaterLevelMarker` → `...-waterlevelmarker`, `WaterLevelMotion` →
  `...-waterlevelmotion`, and `TuningForkTubeSetup` →
  `...-tuningforktubesetup`.
- Assumption predicates: `MatchesProblemAndFigureData` →
  `...-matchesproblemandfiguredata`, `HasStandardAirSoundSpeed` →
  `...-hasstandardairsoundspeed`, `HasPhysicalWaveParameters` →
  `...-hasphysicalwaveparameters`, and `SatisfiesClosedOpenAirColumnLaws` →
  `...-satisfiesclosedopenaircolumnlaws`.
- Derived lemmas: `successiveResonanceSpacing` →
  `lem:physics:phyx-mini-0223:phyxminiproblems-problemphyxmini0223-successiveresonancespacing`,
  `soundWavelength_meters_eq` →
  `lem:physics:phyx-mini-0223:phyxminiproblems-problemphyxmini0223-soundwavelength-meters-eq`,
  and `tuningForkFrequency_hertz_eq` →
  `lem:physics:phyx-mini-0223:phyxminiproblems-problemphyxmini0223-tuningforkfrequency-hertz-eq`.
- Answer semantics: `AnswerChoice` → `...-answerchoice`,
  `AnswerChoice.hertz` → `...-answerchoice-hertz`, `recordedAnswerChoice` →
  `...-recordedanswerchoice`, and `MatchesAnswerChoice` →
  `...-matchesanswerchoice`.
- `problem_phyx_mini_0223` corresponds to
  `thm:physics:phyx_mini_0223:target`.

The blueprint itself was not edited because the task's explicit write permissions protect blueprint chapters. An orchestrator or plan agent with blueprint write permission should add `\leanok` to that environment.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- Natural language: `resonance frequencies of an air column in a tube closed at one end odd quarter wavelength`.
- Natural language: `acoustic wave speed equals frequency times wavelength`.
- Likely concepts/names: `Dimensionful WithDim DimSpeed UnitChoices.SI length frequency speed`.
- Likely name: `WithDim`.
- Natural language plus likely name: `frequency units hertz inverse time Dimensionful`.
- Gap check: `closed open tube acoustic resonance`.

Candidates inspected in detail:

- `Dimensionful` (LeanExplore id 394284) from
  `Physlib.Units.Basic`: its source defines coherent quantities as
  unit-choice-indexed values satisfying `HasDimension`; it is used for
  length and cyclic frequency.
- `UnitChoices.SI` (id 394270) from `Physlib.Units.Basic`: its source
  selects metres, seconds, kilograms, coulombs, and kelvin; it is used for
  all named SI readouts.
- `WithDim` (id 394425) from `Physlib.Units.WithDim.Basic`: its source
  tags an underlying value with a physical `Dimension`; it is used with
  `L𝓭` and `T𝓭⁻¹`.
- `DimSpeed` (id 394481) from `Physlib.Units.WithDim.Speed`: its source
  is `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`; it is used as the acoustic
  propagation-speed type.
- `ClassicalMechanics.WaveEquation` and `UnitExamples.SpeedEq` surfaced
  in the acoustic-law search but are near misses: the former is a PDE-level
  wave equation, while the latter is the speed-distance-time relation rather
  than `v = f λ`.
- The air-column resonance search returned parity and harmonic-oscillator
  declarations, not an API for one-open/one-closed acoustic modes.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, and `DimSpeed`.
- Mathlib: `NNReal` for nonnegative scalar representatives and `ℝ` for named coherent scalar readouts.

All used names and syntax were confirmed by compiling the assigned file with:

```text
lake env lean PhyXMiniProblems/problem_phyx_mini_0223.lean
```

The command exits successfully with only the four expected `declaration uses sorry` warnings.

## Local abstractions introduced

- No dedicated Physlib closed-open air-column resonance API was found, so `SatisfiesClosedOpenAirColumnLaws` states the boundary behavior, odd-quarter-wave resonance condition, and `v = f λ` law explicitly.
- `TuningForkTubeSetup` keeps fork frequency, wavelength, speed, end correction, measured column lengths, mode numbers, and figure geometry as distinct physical roles.
- The answer-choice layer is separate from the physical premises and expresses whole-hertz display/rounding semantics.

These abstractions preserve physical meaning while keeping scalar real numbers confined to SI readouts, dimensionless mode coefficients, and answer values.

## Grounding gaps

- LeanExplore exposed general wave-equation and unit infrastructure but no declaration for resonance modes of a tube open at one end and water-closed at the other.
- No ready-made Physlib dimensionful cyclic-frequency alias or hertz constant was found. `FrequencyQuantity := Dimensionful (WithDim T𝓭⁻¹ NNReal)` is therefore used directly.
- The `archon dag-query` executable was not available on `PATH`, so the
  read-only graph command could not be run. Local dependencies were instead
  checked from the blueprint's explicit `\uses{...}` edges.

## Redraft requests

- None for the Lean statement. The protected blueprint environment still needs `\leanok` from an agent with blueprint write permission.
- The requested `.archon/AGENTS.md` role file is absent from this checkout;
  the stage instructions in the task prompt and `.archon/PROGRESS.md` were
  followed directly.
