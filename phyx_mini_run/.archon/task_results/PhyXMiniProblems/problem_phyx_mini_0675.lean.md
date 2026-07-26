# Prover result: `problem_phyx_mini_0675.lean`

## Status

Complete. Both `sorry` placeholders were replaced by sound proofs without
changing either declaration signature.

## Proofs completed

- `blueBeadTravelTime_squared`: unfolds the physical-parameter, frictionless
  dynamics, and constant-acceleration hypotheses; proves `sin θ > 0` on the
  stated acute branch; cancels the positive denominator `g * sin θ`; and
  derives `t² = 2L / (g sin θ)` by nonlinear arithmetic.
- `problem_phyx_mini_0675`: uses the nonnegativity of the `NNReal`-valued
  dimensionful time readout and `Real.sqrt_sq` to select the nonnegative root
  of the squared-time relation.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0675.lean` succeeded.
- Lean LSP diagnostics report no errors. The only warning is that the frozen
  figure hypothesis `h_figure` is not explicitly referenced by the final
  algebraic proof.
- Source scans report no `sorry`, `admit`, new `axiom`, `sorryAx`, or
  `native_decide`.
- Axiom verification for both completed declarations reports only Lean's
  standard `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` reports no whitespace errors.

## Blueprint marker readiness

The blueprint environments for `blueBeadTravelTime_squared` and
`problem_phyx_mini_0675` are ready for `\leanok`. The chapter was not edited
because prover write permissions restrict this task to the assigned Lean file
and this result report; the synchronization/review phase should apply the
markers.

## Project notes

- The requested `.archon/AGENTS.md` is absent from this checkout. The available
  `.archon/prover-modes/physics.md`, injected prover instructions,
  `.archon/PROGRESS.md`, iteration plan, blueprint chapter, source report,
  grounding log, and autoformalization report were read and followed.
- The assigned Lean file contains no `/- USER: ... -/` comments.

## Redraft needed

None.

---

# Prior autoformalization result: `problem_phyx_mini_0675.lean`

## Assumption/target split

### Governing laws

- `ObeysFrictionlessInclinedRodDynamics` states that the blue bead is released
  from rest and that its constant tangential acceleration toward `C` is the
  gravitational component `g * sin θ` along the straight inclined rod.
- `ObeysConstantAccelerationKinematics` states the independent kinematic law
  `L = u * t + (1/2) * a * t^2` over the complete trip from `B` to `C`.
- `HasPhysicalParameters` supplies only nondegeneracy: positive ring radius,
  positive rod lengths, positive gravitational acceleration, and the acute
  branch `0 < θ < π/2` shown in the bitmap.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemAndPrimaryFigure` records the vertical ring plane, the rods
  `AC` and `CB`, labels `D` and `L`, the rods' vertical/inclined directions,
  all three points on the circular ring, fastening within the ring, the dashed
  `AB` segment, and the initial/destination points and rod constraints for the
  red and blue beads.
- The primary bitmap shows `A` at the top, `C` at the bottom, and the vertical
  rod `AC` spanning the ring, so its SI length readout is recorded as twice the
  ring-radius readout.
- `inclinationAngleRad` is a dimensionless radian readout. Length, time, speed,
  and acceleration remain Physlib `Dimensionful` quantities; only their SI
  projections are real scalars.

### Current target conclusions

- `blueBeadTravelTime_squared` derives
  `t^2 = 2 * L / (g * sin θ)` from the two governing-law predicates.
- `problem_phyx_mini_0675` concludes
  `t = Real.sqrt (2 * L / (g * sin θ))`, the recorded answer choice C and the
  declaration corresponding to `thm:physics:phyx_mini_0675:target`.

## Goal-faithfulness audit

The requested square-root expression does not occur in
`InclinedRodBeadSetup`, `MatchesProblemAndPrimaryFigure`,
`HasPhysicalParameters`, `ObeysFrictionlessInclinedRodDynamics`, or
`ObeysConstantAccelerationKinematics`. The setup contains a genuine unknown
dimensionful travel time. The premises give only the figure, physical branch,
release-from-rest condition, tangential force law, and general
constant-acceleration displacement law. The squared relation and final
square-root relation occur only as conclusions of a lemma and theorem,
respectively. No answer-choice predicate, unfolding definition, reflexive
equality, or `True` proposition makes the target automatic.

## Declarations and blueprint labels

- Dimensionful types: `LengthQuantity`, `TimeQuantity`, `SpeedQuantity`, and
  `AccelerationQuantity`.
- SI readouts: `lengthInMeters`, `timeInSeconds`,
  `speedInMetersPerSecond`, and `accelerationInMetersPerSecondSquared`.
- Figure vocabulary: `FigurePoint`, `Rod`, `Bead`, `RodDirection`,
  `PlaneOrientation`, and `CircularRing`.
- Physical model: `InclinedRodBeadSetup`,
  `MatchesProblemAndPrimaryFigure`, `HasPhysicalParameters`,
  `ObeysFrictionlessInclinedRodDynamics`, and
  `ObeysConstantAccelerationKinematics`.
- Derived helper: `blueBeadTravelTime_squared` (no separate blueprint label).
- Main declaration:
  `PhyXMiniProblems.ProblemPhyXMini0675.problem_phyx_mini_0675` corresponds to
  `thm:physics:phyx_mini_0675:target`.

## LeanExplore queries and candidates

Queries were run with `packages: ["Mathlib", "Physlib"]` as required:

- Natural-language query: `frictionless bead sliding along an inclined rod
  under gravity constant acceleration`. Nearby results included
  `UnitExamples.NewtonsSecondWithDim'`,
  `ClassicalMechanics.SlidingPendulum.ConfigurationSpace`, and
  `ClassicalMechanics.FreeParticle.NewtonsSecondLaw`; none has the constrained
  straight-rod bead law required here.
- Natural-language query: `one dimensional constant acceleration displacement
  from rest`. Results included rigid-body displacement declarations but no
  ready-made scalar kinematic theorem matching this model.
- Natural-language query: `physical dimensions SI units length time
  acceleration`. This grounded `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  and `UnitChoices.SI`.
- Likely-name queries: `Dimensionful WithDim`, `Dimension.T𝓭`,
  `UnitChoices.SI`, `Real.sin`, and `Real.sqrt`.
- Source, module, and docstring were fetched for the candidates actually used:
  `Dimensionful`, `Dimension.L𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`,
  `Real.sin`, and `Real.sqrt`.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, and
  `UnitChoices.SI`.
- Mathlib: `Real.sin`, `Real.pi`, `Set.Ioo`, and `Real.sqrt`.
- `Real.sqrt` is provided by `Mathlib.Analysis.Real.Sqrt`; `Real.sin` is
  provided through Mathlib's trigonometric API. Physlib's dimension and SI
  declarations are available through `Physlib.Units.WithDim.Basic`.

## Local abstractions introduced

- The enums and `CircularRing` preserve the labeled geometry and distinguish
  the physical rods and beads instead of reducing them to scalar aliases.
- `InclinedRodBeadSetup` keeps physical quantities dimensionful while exposing
  only explicit SI readout functions for formulas.
- The two governing-law predicates are local because LeanExplore found no
  compatible ready-made model for a frictionless bead constrained to a fixed
  straight rod. They state standard mechanics laws independently of the
  requested closed form.

## Grounding gaps

- No direct Mathlib/Physlib declaration was found for frictionless motion of a
  bead on an inclined straight rod or for the exact `L = u t + (1/2) a t^2`
  interval law, so faithful local predicates were required.
- The requested `.archon/AGENTS.md` is absent from this project checkout. The
  available `.archon/prover-modes/physics-formalize.md` was read and followed.
- The prompt says `archon` is on `PATH`, but the executable was unavailable, so
  the read-only dependency-graph query could not be performed. The blueprint
  target has no declared prior-part dependencies in the source report.

## Redraft / orchestration notes

- LSP diagnostics report only the two expected `declaration uses sorry`
  warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0675.lean` exits with code
  zero and reports the same two expected warnings.
- The chapter already exists and is marked `% archon:physics`.
- The blueprint theorem still needs `\leanok` added by an agent permitted to
  edit blueprint chapters. This task's explicit write permissions prohibit
  editing the chapter itself.
