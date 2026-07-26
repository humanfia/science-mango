# Autoformalization result: `problem_phyx_mini_0227.lean`

Status: `PhyXMiniProblems/problem_phyx_mini_0227.lean` compiles with one expected
warning, for the `sorry` body of the blueprint target theorem, and no errors.

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was used.

## Physical model extracted

- The primary image shows a pivot at the upper end of a straight, very light
  support rod labeled `0.500 m`.
- The rod's lower end is attached to one end of a collinear meterstick. A
  meterstick supplies the `1.00 m` stick length, but the source does not identify
  which numbered mark is at the junction; the formal label is therefore only
  `MeterstickEnd.rodSide`.
- The meterstick is modeled as uniform and the very light rod as having
  negligible (zero idealized) mass.
- The meterstick center is `L/2` from its attached end, hence its center of mass
  is at `r + L/2` from the pivot.
- The uniform-stick central inertia is `M L^2 / 12`; the pivot inertia is
  obtained by the parallel-axis law `I_p = I_cm + M d^2`.
- In the small-angle regime, the physical pendulum is a linear angular
  oscillator with generalized inertia `I_p` and gravitational restoring
  coefficient `M g d`.
- The `1.00 m` reference simple pendulum is a linear angular oscillator with
  generalized inertia `m L^2` and restoring coefficient `m g L`; its arbitrary
  positive bob mass cancels from the comparison.
- The requested quantity is the absolute period difference as a percentage of
  the reference period. The exact period ratio is `sqrt (13/12)`, whose
  percentage excess rounds to `4.08%`.

## Assumption/target split

### Governing laws

- `SatisfiesPendulumLaws.centerOfMassGeometry` states
  `d = r + L/2`.
- `uniformMeterstickCenterInertia` states the uniform-stick law
  `I_cm = M L^2 / 12`.
- `parallelAxisLaw` states `I_p = I_cm + M d^2`.
- `physicalGeneralizedInertia` and
  `physicalGravitationalRestoringCoefficient` connect the physical pendulum's
  scalar angular oscillator to `I_p` and `M g d`.
- `referenceGeneralizedInertia` and
  `referenceGravitationalRestoringCoefficient` connect the simple pendulum's
  scalar angular oscillator to `m L^2` and `m g L`.
- `physicalSmallAnglePeriod` and `referenceSmallAnglePeriod` use Physlib's
  harmonic-oscillator period for the two linearized angular models.

### Previous-part results

- None. The source report records no previous parts, and no previous result is
  assumed.

### Figure/data readouts and modeling data

- `MatchesMeterstickPendulumFigure` records the `0.500 m` support-rod label, the
  `1.00 m` meterstick length, pivot at the rod's upper end, junction at its lower
  end and the meterstick's rod-side end, and collinearity.
- `HasMeterstickPendulumProblemData` records negligible support-rod mass,
  uniform meterstick mass distribution, the release angle's downward-vertical
  reference and qualitative small-angle regime, a `1.00 m` reference-pendulum
  length, and positivity of the meterstick mass, reference bob mass, and
  gravitational acceleration.
- `recordedAnswerChoice = .D` is dataset metadata, not a physical law.
- All four displayed percentages are recorded by `AnswerChoice.percent`.

### Current target conclusions

`periodDifference_matches_recordedAnswerD` concludes all of the following:

- the exact period ratio is `sqrt (13/12)`;
- the meterstick assembly's period is longer than the reference period;
- its percentage difference rounds to the same hundredth of a percent as
  recorded answer D (`4.08%`);
- answer D is at least as close as every displayed alternative.

## Goal-faithfulness audit

No current target conclusion occurs in `MeterstickPendulumSetup`,
`MatchesMeterstickPendulumFigure`, `HasMeterstickPendulumProblemData`, or
`SatisfiesPendulumLaws`. In particular, none of those declarations mentions
`13/12`, `4.08`, a period ratio, a percentage difference, or answer D.

`periodDifferencePercent`, `RoundsToDisplayedPercentage`, and
`IsClosestDisplayedPercentage` are generic readout/comparison definitions;
unfolding them does not prove that this apparatus has the recorded result.
`recordedAnswerChoice` merely transcribes supplied dataset metadata. The exact
ratio, strict comparison, rounding relation, and closest-choice claim remain
substantive conclusions of the theorem.

## Declarations created and blueprint correspondence

- Dimensionful roles: `LengthQuantity`, `TimeQuantity`, `MassQuantity`,
  `AccelerationQuantity`, and `MomentOfInertiaQuantity`.
- Coherent SI projections: `lengthInMeters`, `timeInSeconds`,
  `massInKilograms`, `accelerationInMetersPerSecondSquared`, and
  `momentOfInertiaInKilogramMeterSquared`.
- Figure labels: `SuspensionRodEnd`, `MeterstickEnd`, `ComponentAlignment`,
  `AngleReferenceDirection`, and `StickMassDistribution`.
- Apparatus/model interfaces: `MeterstickPendulumSetup`,
  `MatchesMeterstickPendulumFigure`, `HasMeterstickPendulumProblemData`, and
  `SatisfiesPendulumLaws`.
- Answer reporting: `periodDifferencePercent`, `AnswerChoice`,
  `AnswerChoice.percent`, `recordedAnswerChoice`,
  `RoundsToDisplayedPercentage`, and `IsClosestDisplayedPercentage`.
- `periodDifference_matches_recordedAnswerD` corresponds to
  `thm:physics:phyx_mini_0227:target`.

The supporting declarations belong to the same single target environment; the
chapter provides no separate blueprint labels for them.

## LeanExplore queries and candidates actually used

Searches were run with package filters `Mathlib` and `Physlib`.

- Natural-language queries:
  - `physical pendulum small angle period moment of inertia center of mass`
  - `simple pendulum period length gravity`
  - `SI units length mass time moment of inertia dimensional quantity`
  - `Real.sqrt pi period percentage difference`
  - `physical pendulum`
  - `parallel axis theorem moment of inertia`
  - `uniform rod moment of inertia`
- Likely-name/API queries:
  - `Dimensionful WithDim UnitChoices.SI`
  - `Dimension.L𝓭 Dimension.M𝓭 Dimension.T𝓭`
  - `Dimension.M𝓭 Dimension.T𝓭`
  - `ClassicalMechanics.HarmonicOscillator`
  - `ClassicalMechanics.HarmonicOscillator.period`
  - `ClassicalMechanics.HarmonicOscillator structure mass spring constant angular frequency`
  - `RigidBody.small_oscillations_about_equilibrium`
  - `Int round real nearest integer`

Source/module data was fetched for the candidates used or assessed directly:

- `Dimensionful` (Physlib, `Physlib.Units.Basic`)
- `UnitChoices.SI` (Physlib, `Physlib.Units.Basic`)
- `Dimension.L𝓭`, `Dimension.M𝓭`, and `Dimension.T𝓭`
  (Physlib, `Physlib.Units.Dimension`)
- `ClassicalMechanics.HarmonicOscillator`
  (Physlib, `Physlib.ClassicalMechanics.HarmonicOscillator.Basic`)
- `ClassicalMechanics.HarmonicOscillator.period`
  (Physlib, `Physlib.ClassicalMechanics.HarmonicOscillator.Solution`)
- `Real.sqrt` (Mathlib, `Mathlib.Analysis.Real.Sqrt`)
- `round` (Mathlib, `Mathlib.Algebra.Order.Round`)
- `RigidBody.parallel_axis_theorem` and
  `RigidBody.small_oscillations_about_equilibrium`
  (Physlib, `Physlib.ClassicalMechanics.RigidBody.Basic`), both assessed as
  non-usable `informal_lemma` declarations.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `UnitChoices.SI`, `Dimension.L𝓭`,
  `Dimension.M𝓭`, `Dimension.T𝓭`,
  `ClassicalMechanics.HarmonicOscillator`, and
  `ClassicalMechanics.HarmonicOscillator.period`.
- Mathlib: `Real.sqrt` and `round`.

## Local abstractions introduced

- The five quantity aliases retain Physlib dimension tags and unit-system
  behavior; they are not transparent scalar aliases or one-field scalar
  wrappers.
- Apparatus-end, alignment, angle-reference, and mass-distribution inductives
  preserve the labels and qualitative geometry supplied by the source.
- `releaseIsInSmallAngleRegime : Prop` preserves the qualitative word “small”
  without inventing an unsupported numerical angular cutoff.
- `SatisfiesPendulumLaws` provides the missing executable scalar laws for a
  uniform stick's inertia, the parallel-axis shift, and gravitational angular
  restoring coefficients. These are governing relations and contain none of
  the requested percentage result.
- Physlib's scalar `HarmonicOscillator` is used as the linearized generalized
  angular oscillator. Explicit law fields connect its positive scalar `m` and
  `k` to dimensionful generalized inertia and torque-coefficient readouts.

## Grounding gaps and redraft requests

- LeanExplore found no executable Physlib declaration specialized to the
  small-angle physical-pendulum period or a uniform thin rod/meterstick moment
  of inertia.
- `RigidBody.parallel_axis_theorem` and
  `RigidBody.small_oscillations_about_equilibrium` exist only as
  `informal_lemma`s, so they cannot ground executable Lean propositions. The
  faithful scalar governing-law fields above fill this gap.
- The required `.archon/AGENTS.md` file is absent from this project. The
  available `.archon/prover-modes/physics-formalize.md` was read and followed
  instead.
- The prompt states that `archon` is on `PATH`, but both requested DAG commands
  failed with `archon: command not found`; no dependency information could be
  obtained from `leandag`.
- The blueprint chapter exists, but it was not edited to add `\leanok` because
  this task's explicit write permissions prohibit editing blueprint chapters.
  The plan/blueprint owner should add `\leanok` to
  `thm:physics:phyx_mini_0227:target` after accepting this formalization.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0227.lean`: success, with
  only the expected theorem `sorry` warning.
- `archon-lean-lsp` diagnostics: success, with the same single `sorry` warning
  and no failed dependencies.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0227.lean`: clean.
