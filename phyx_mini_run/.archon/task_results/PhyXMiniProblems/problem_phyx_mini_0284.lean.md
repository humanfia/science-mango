# Autoformalization result: `problem_phyx_mini_0284.lean`

## Review-gate repair and source audit

The iteration-001 gate reason was that no genuine post-formalization task
result existed.  This report records the searches and declarations actually
used after the Lean model was written, together with the required
assumption/target split.

The source report and primary raster `phyx_data/test_image/284.png` were
inspected.  The prose supplies `2500 kg` and `17 m`; the raster shows the
swinging cable segment running from the top crane pulley to the demolition
ball beside the brick wall, plus the tracked crane and a faint cityscape.  It
contains no printed numerical labels.  The source report lists no previous
parts.  The recorded answer D is physically consistent with the governing
law: `2π * sqrt (17 / 9.8) ≈ 8.275443753279 s`, whose distance from `8.3 s` is
approximately `0.024556246721 s`.

## Assumption/target split

### Governing laws

- `UsesStandardEarthGravity setup` supplies the ordinary near-Earth textbook calibration `g = 9.8 m/s²`, which is implicit rather than printed in the source.
- `SatisfiesSmallAngleSimplePendulumPhysics setup` records the point-mass bob, massless inextensible cable, and small-angle idealizations.
- Its `smallAnglePeriodLaw` field is the symbolic governing relation
  `T = 2 * Real.pi * Real.sqrt (L / g)`. It contains neither the substituted cable length nor the recorded numerical answer.
- `HasPhysicalParameters setup` records positivity of mass, cable length, gravity, and period.

### Previous-part results

- None. The source report has no previous parts.

### Figure/data readouts

- The prose data are the demolition-ball mass `2500 kg` and swinging cable length `17 m`.
- The primary image is represented by the tracked crane vehicle, crane arm, pivot pulley, swinging cable segment, demolition ball, brick wall, and cityscape background.
- The figure predicate records that the cable joins the crane pivot to the ball attachment, the ball is adjacent to the wall, and the bitmap contains no printed text.
- The four displayed answer values are represented separately by `answerPeriodSeconds`.

### Current target conclusions

- The period readout rounds to the displayed `8.3 s` value for answer D, formalized by `RoundsToDisplayedTenth` with strict error below `0.05 s`.
- Answer D is strictly closer to the computed period than each of A, B, and C, formalized by `IsUniqueClosestAnswerChoice`.

## Goal-faithfulness audit

The period is an independent `TimeQuantity` field of the setup and is not defined as `8.3 s`. Neither `MatchesProblemAndFigureData`, `UsesStandardEarthGravity`, `HasPhysicalParameters`, nor `SatisfiesSmallAngleSimplePendulumPhysics` asserts rounding to `8.3 s` or selection of D. The governing-law structure contains only the general formula in the variables `L` and `g`; the theorem must combine that law with the `17 m` and `9.8 m/s²` readouts and establish the numerical bounds. The answer-choice table merely transcribes source display data and does not make either target proposition true by unfolding.

The `2500 kg` mass is retained as a dimensionful setup quantity and source datum even though the simple-pendulum law is mass-independent. Thus the physical setup is not weakened to only the two scalars appearing in the final calculation.

## Declarations created and blueprint correspondence

- Dimension/quantity layer: `accelerationDimension`, `MassQuantity`, `LengthQuantity`, `AccelerationQuantity`, `TimeQuantity`, `quantitySIReadout`, and the four named SI readout functions.
- Figure layer: `FigureObject`, `FigurePoint`, and `DemolitionCraneFigure`.
- Model layer: `BobModel`, `CableModel`, `OscillationRegime`, and `DemolitionBallPendulumSetup`.
- Assumption layer: `MatchesProblemAndFigureData`, `UsesStandardEarthGravity`, `HasPhysicalParameters`, and `SatisfiesSmallAngleSimplePendulumPhysics`.
- Answer layer: `AnswerChoice`, `answerPeriodSeconds`, `RoundsToDisplayedTenth`, and `IsUniqueClosestAnswerChoice`.
- `demolitionBallSwingPeriod_is_answer_D` corresponds to `thm:physics:phyx_mini_0284:target`.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- Natural language: `simple pendulum small angle period equals two pi square root length divided by gravitational acceleration`.
- Likely names: `Pendulum.period SimplePendulum smallAnglePeriod`.
- Units/concepts: `physical quantities SI units dimensions length mass time gravitational acceleration`, `Dimensionful WithDim UnitChoices.SI`, `WithDim scaleUnit_val`, and `Dimension.M𝓭 Dimension.T𝓭`.
- Analysis names: `Real.sqrt Real.pi abs`, `Real.pi`, and `abs absolute value real number`.
- Near-match check: `ClassicalMechanics.HarmonicOscillator.period period_eq`.

Candidates whose source/module information grounded the file were:

- `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, and `Dimension.T𝓭` from `Physlib.Units.Dimension`.
- `UnitChoices.SI` and `Dimensionful` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt` and `Real.pi` from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

`ClassicalMechanics.HarmonicOscillator.period` and `period_eq` were inspected as near matches. They express `2π/ω` for Physlib's harmonic-oscillator structure but do not supply the pendulum-specific relation `ω² = g/L`, so they were not imported or used.
`WithDim.scaleUnit_val` was also returned while checking the unit-scaling API,
but the final SI readout only needs direct evaluation at `UnitChoices.SI` and
the `WithDim.val` projection.

## Physlib/Mathlib names grounded

The physical primitives use Physlib's unit-independent `Dimensionful (WithDim d NNReal)` representation and coherent `UnitChoices.SI` evaluation. The formula uses Mathlib's actual `Real.pi` and `Real.sqrt`. Compilation verified every referenced name and import.

## Local abstractions introduced

- The figure object/point types preserve the qualitative image geometry without inventing nonexistent numerical image labels.
- The three modeling enums distinguish the point-mass, cable, and small-angle idealizations from the raw apparatus data.
- `SatisfiesSmallAngleSimplePendulumPhysics` is a local governing-law interface because the searched libraries provide no dedicated small-angle simple-pendulum period theorem.
- The rounding and closest-choice predicates preserve the fact that `8.3 s` is a rounded multiple-choice answer rather than an exact equality to `2π√(17/9.8)`.

## Grounding gaps and redraft notes

- LeanExplore exposed pendulum configuration spaces and a harmonic-oscillator period API, but no reusable simple-pendulum law relating length, gravity, and period. The local symbolic law is therefore necessary.
- The prompt-listed `.archon/AGENTS.md` is absent. The available `.archon/prover-modes/physics-formalize.md` supplied the stage-specific role instructions.
- The `archon` executable was not available on `PATH`, so dependency-graph queries could not be run. The source report and chapter declare no previous-part dependencies.
- The blueprint chapter already exists. It was not edited to add `\leanok` because the task's explicit write permissions forbid prover edits to blueprint chapters; the project's marker synchronization should add it.

## Verification

- `archon-lean-lsp` diagnostics: one expected `declaration uses 'sorry'` warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0284.lean`: exit code 0 with only the expected `sorry` warning.
- Independent numerical sanity check: `2π * sqrt (17 / 9.8) =
  8.275443753279...`, within `0.05 s` of answer D.
