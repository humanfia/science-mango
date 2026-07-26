# Autoformalization result: `problem_phyx_mini_0233.lean`

## Assumption/target split

### Governing laws

- A point bob on a rigid massless rod has pivot moment of inertia `M L^2`.
- In the small-angle regime, the spring attachment's horizontal displacement per radian is `h`.
- Hooke's law gives spring force per radian as `k` times that displacement.
- The lever arm `h` converts the spring force coefficient into a spring rotational-stiffness coefficient.
- Linearized gravity contributes rotational stiffness `M g L`.
- Gravitational and spring restoring-torque coefficients add.
- The generalized angular oscillator obeys Physlib's `omega = sqrt (K / I)` relation unitwise.
- Angular and cyclic frequency obey `omega = 2 pi f`.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- The primary image shows a pivot, rigid rod, bob, spring, and fixed right wall.
- The equilibrium rod is vertical and the equilibrium spring is horizontal.
- The spring attaches to the rod at distance `h` below the pivot and to the fixed wall.
- The printed labels are rod length `L`, attachment distance `h`, bob mass `M`, spring constant `k`, and angle `theta`.
- The rod's own mass is ignored, the rod is rigid, and the oscillation is in the small-angle regime.
- The spring is modeled as relaxed at the depicted vertical equilibrium, the standard ideal-spring condition required for that configuration to be torque-free.
- Physical nondegeneracy assumptions state `M > 0`, `L > 0`, `h > 0`, `h <= L`, `g > 0`, `k > 0`, and positivity of the modeled inertia, total rotational stiffness, and frequencies.

### Current target conclusions

- Derive the spring rotational stiffness `k h^2` from the small-angle geometry, Hooke law, and moment arm.
- Derive
  `f = (1 / (2 pi L)) * sqrt (g L + k h^2 / M)`
  in every coherent unit system.
- Conclude that the modeled frequency matches printed answer choice `D`.

## Goal-faithfulness audit

The requested closed frequency and answer-choice `D` occur only in derived lemma/theorem conclusions and answer-list metadata. `SpringPendulumSetup` stores independent frequency quantities rather than defining either frequency by the answer. `MatchesProblemAndSuppliedFigure` contains only source/figure modeling facts. `SatisfiesSmallAngleTorqueLaws` factors the spring contribution through an attachment-displacement coefficient and a force coefficient; it does not assume `k h^2`. `SatisfiesSmallAngleFrequencyLaws` states only the general generalized-SHO law and `omega = 2 pi f`; it does not mention `L`, `h`, `M`, `g`, choice `D`, or the final closed form. No premise contains `MatchesAnswerChoice`.

The definition `displayedAnswerFrequencyReadout` is a literal transcription of answer-list metadata. In particular, the three dimensionally inconsistent distractors are represented only as scalar printed formulas and are never physical-law assumptions.

## Declarations created and blueprint correspondence

- Dimensionful quantity types and coherent-unit readouts for mass, length, acceleration, force, spring constant, moment of inertia, rotational stiffness, cyclic frequency, and angular frequency.
- Figure/model enums and `SpringPendulumFigure` for the labels and qualitative geometry visible in `233.png`.
- `SpringPendulumSetup`, `MatchesProblemAndSuppliedFigure`, and `HasPhysicalSpringPendulumParameters` for the physical setup and data.
- `SatisfiesSmallAngleTorqueLaws` for rigid-body geometry, Hooke's law, gravity torque, and addition of restoring torques.
- `effectiveAngularOscillatorInUnits` and `SatisfiesSmallAngleFrequencyLaws` for the generalized harmonic-oscillator dynamics.
- `springRotationalStiffness_eq_k_mul_h_sq` and `smallAngle_vibrationFrequency_formula` as derived targets.
- `AnswerChoice`, `displayedAnswerFrequencyReadout`, `recordedDatasetAnswerChoice`, and `MatchesAnswerChoice` for the multiple-choice metadata.
- `problem_phyx_mini_0233` corresponds to blueprint label `thm:physics:phyx_mini_0233:target`.

## LeanExplore grounding

Queries were run with `packages: ["Mathlib", "Physlib"]`:

- `physical dimensions and SI units for mass length time frequency force and spring constant`
- `WithDim UnitWithDim Length Mass Time Frequency`
- `small angle pendulum harmonic oscillator angular frequency`

Candidates inspected and used:

- `Dimension` (ID 394292), `Dimension.L𝓭` (ID 394324), and `Dimension.M𝓭` (ID 394336), from `Physlib.Units.Dimension`.
- `Dimensionful` (ID 394284) and `UnitChoices.SI` (ID 394270), from `Physlib.Units.Basic`. The formalization uses `Dimensionful`; generic coherent `UnitChoices` readouts make a dedicated SI-only bridge unnecessary.
- `ClassicalMechanics.HarmonicOscillator.ω` (ID 385208), from `Physlib.ClassicalMechanics.HarmonicOscillator.Basic`, whose source defines `omega` as `sqrt (k / m)`.

Near matches inspected but not directly used:

- `ClassicalMechanics.DampedHarmonicOscillator.k_eq_m_mul_ω_sq` (ID 385142) concerns a damped translational oscillator, while this problem is an undamped rotational generalized-coordinate system.
- `ClassicalMechanics.HarmonicOscillator.period` (ID 385345) gives `2 pi / omega`; the problem asks for cyclic frequency, so the direct governing bridge `omega = 2 pi f` is clearer.

## Physlib/Mathlib names grounded

- `Dimensionful`
- `WithDim`
- `Dimension.L𝓭`, `Dimension.T𝓭`, and `Dimension.M𝓭`
- `UnitChoices`
- `ClassicalMechanics.HarmonicOscillator`
- `ClassicalMechanics.HarmonicOscillator.ω`
- `Real.sqrt`
- `Real.pi`

## Local abstractions introduced

- Dimensionful aliases distinguish acceleration, force, spring stiffness, moment of inertia, rotational stiffness, and the two frequency roles while retaining Physlib's unit-scaling semantics.
- `SpringPendulumFigure` preserves the actual figure labels, attachments, and orientations without treating image content as numerical data.
- Explicit displacement-per-radian and force-per-radian quantities preserve the small-angle geometry and Hooke-law route to `k h^2`; this prevents the answer-specific spring term from being assumed.
- Physlib has no specialized spring-coupled simple-pendulum object. `effectiveAngularOscillatorInUnits` therefore uses Physlib's scalar harmonic-oscillator equation only as a unitwise generalized-coordinate view, while the physical generalized mass `I` and stiffness `K` remain separately dimension-tagged.

## Grounding gaps and redraft requests

- LeanExplore found no specialized Physlib declaration for a small-angle pendulum with a spring attached partway down a rigid rod. The faithful local torque-law interface above fills this gap.
- `.archon/AGENTS.md` was absent from the project. The available `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- The `archon` executable was not available on `PATH`, so the optional dependency-graph queries could not be completed.
- The blueprint environment still needs `\leanok`. The task explicitly forbids editing blueprint chapters, so the orchestrator/plan agent should add it to `thm:physics:phyx_mini_0233:target`.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0233.lean` exits with status 0. The only diagnostics are the three expected `declaration uses sorry` warnings for the two derived lemmas and the final theorem.
