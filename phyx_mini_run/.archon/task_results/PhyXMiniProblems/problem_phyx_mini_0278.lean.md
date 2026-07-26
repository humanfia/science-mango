## Assumption/target split

### Governing laws

- `SatisfiesIdealTorsionPendulumLaws.oscillatorMassParameterIsMomentOfInertia` identifies the first positive scalar parameter of Physlib's one-coordinate oscillator with the SI moment-of-inertia readout.
- `SatisfiesIdealTorsionPendulumLaws.oscillatorStiffnessParameterIsTorsionConstant` identifies the second positive scalar parameter with the SI torsion-constant readout.
- `SatisfiesIdealTorsionPendulumLaws.linearTorqueMagnitudeLaw` states the graph's linear law `|tau(theta)| = kappa theta` on the displayed nonnegative-angle interval.
- `amplitudeMatchesReleaseAngle`, `releasePhaseIsZero`, and `angularPositionIsHarmonicTrajectory` state the ideal undamped cosine motion associated with release from the positive turning point.
- `angularVelocityIsTimeDerivative` states that the signed angular-velocity readout is `dtheta/dt` via Mathlib's `HasDerivAt`.

### Previous-part results

- None. The source report records no previous parts.

### Figure/data readouts

- The apparatus contains the metal disk, central wire, and two clamps; the wire passes through the disk center, is soldered to it, is vertical, is clamped at both ends, and is taut.
- The problem data give `tau_s = 4/1000 N m`, `t_s = 2/5 s`, release angle `1/5 rad`, initial angular position equal to that release angle, and zero initial angular velocity.
- `MatchesSuppliedFigure` records all four axis labels, both curve kinds, both grids, and both scale markers.
- The upper curve passes through the origin and reaches `tau_s` at the release angle.
- The lower curve is the disk trace; it starts at `+theta_0`, reaches `-theta_0` at `t_s/2`, and returns to `+theta_0` at `t_s`. Consequently, the marked max-to-max scale is recorded as one Physlib oscillator period.
- `HasPhysicalTorsionPendulumParameters` supplies only positivity/nondegeneracy conditions.

### Current target conclusions

- `IsGreatest (Set.range (fun t => |omega_disk(t)|)) Real.pi`: the maximum angular speed is exactly `pi rad/s`.
- `MatchesAnswerChoice Real.pi recordedDatasetAnswer`: this exact value rounds to the displayed `3.14 rad/s`, recorded as choice D.

## Goal-faithfulness audit

The setup contains independent angular-position and angular-velocity response functions and has no field for a maximum angular speed. No premise contains `IsGreatest`, the numerical value `pi` as a proposed maximum, `3.14`, or any answer label. The answer table and rounding predicate are used only on the conclusion side of the main theorem.

The figure-period equation is a permitted graph readout: the primary bitmap visibly places `t_s` at the next positive maximum after the maximum at time zero. The cosine trajectory and derivative relation are general governing laws, not definitions of the requested maximum. Establishing the target still requires differentiating the trajectory, using the period definition `T = 2 pi / omega`, proving the absolute sine bound is attained, and checking the rounding tolerance. Thus no target conclusion is obtained by unfolding a local definition or copied into a hypothesis.

## Source/law/answer audit

- Source text: the apparatus description, `tau_s = 4.0e-3 N m`, release angle `0.200 rad`, `t_s = 0.40 s`, and all four displayed choices are represented.
- Primary image: direct inspection confirms the upper line from `(0, 0)` to `(0.20, tau_s)` and the lower trace from the positive turning point at time zero to the next positive turning point at the marker `t_s`, with a negative turning point halfway between. The image also confirms both grids and the printed axis labels.
- Governing law: the ideal undamped torsion law is separated from the image readouts. Physlib's scalar oscillator parameters are bridged explicitly to moment of inertia and torsion stiffness, its cosine trajectory represents the angular coordinate, and Mathlib's derivative predicate identifies the signed angular velocity.
- Answer: amplitude `1/5 rad` and period `2/5 s` support the exact maximum `pi rad/s`, which matches the recorded displayed value `3.14 rad/s` within the stated half-unit-in-the-last-place tolerance. The recorded choice is conclusion metadata, never a physical premise.

## Declarations and blueprint labels

- Supporting physical model: `TimeQuantity`, `MomentOfInertiaQuantity`, `TorqueMagnitudeQuantity`, `TorsionConstantQuantity`, `SignedAngularVelocityQuantity`, and their coherent SI readout functions.
- Apparatus/figure model: `ApparatusComponent`, `GraphPanel`, `AxisDirection`, `FigureAxisLabel`, `CurveKind`, `TorsionPendulumApparatus`, and `SuppliedFigure`.
- Experiment/model interfaces: `TorsionPendulumSetup`, `MatchesProblemData`, `MatchesSuppliedFigure`, `HasPhysicalTorsionPendulumParameters`, and `SatisfiesIdealTorsionPendulumLaws`.
- Answer representation: `AnswerChoice`, `displayedAngularSpeedRadiansPerSecond`, `recordedDatasetAnswer`, and `MatchesAnswerChoice`.
- `PhyXMiniProblems.ProblemPhyXMini0278.problem_phyx_mini_0278` corresponds to `thm:physics:phyx_mini_0278:target`.

The blueprint was not edited to add `\leanok` because this task's explicit write permissions allow edits only to the assigned Lean file and this result file.

## LeanExplore queries and candidates

All searches used `packages: ["Mathlib", "Physlib"]`.

- Query: `torsion pendulum torque angular displacement simple harmonic oscillator`.
  - Used candidates: `ClassicalMechanics.HarmonicOscillator.AmplitudePhase`, `ClassicalMechanics.HarmonicOscillator.ω`, and `ClassicalMechanics.HarmonicOscillator.period`.
  - Inspected but not used directly: `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory`, `trajectory_eq_cos`, and `trajectory_velocity_eq_sin`; their translational trajectory interface does not preserve this problem's explicit angular and dimensionful readout roles as clearly as the local bridge.
- Query: `ClassicalMechanics.HarmonicOscillator period angular frequency amplitude phase`.
  - Confirmed `period`, `AmplitudePhase`, and the related `period_eq`/`period_pos` API.
- Query: `HasDerivAt derivative cosine angular velocity`.
  - Used Mathlib `HasDerivAt` for the kinematic relation.
  - Inspected but did not use `RigidBodyMotion.angularVelocity` because it is a three-dimensional vector angular velocity, while the disk has one signed coordinate about a fixed axis.
- Query: `Dimensionful WithDim SI units mass length time`.
  - Used `Dimensionful` and `UnitChoices.SI`; confirmed the physical-dimension API.
- Exact-name query: `ClassicalMechanics.HarmonicOscillator`.
  - Used candidate: `ClassicalMechanics.HarmonicOscillator`, whose positive fields `m` and `k` are linked explicitly to rotational inertia and torsion constant.
- Query: `WithDim physical dimensions`.
  - Confirmed the tagged-type API; the exact `WithDim` declaration was found by the accompanying dimension-symbol query.
- Query: `Dimension.M𝓭 Dimension.T𝓭`.
  - Used `WithDim`, `Dimension.M𝓭`, and `Dimension.T𝓭`; `Dimension.L𝓭` was grounded by the SI-dimension search.
- Query: `IsGreatest Set.range maximum`.
  - Used Mathlib `IsGreatest` and `Set.range` to state an attained maximum rather than only a supremum.

Source, module, and docstring details were fetched for the candidates actually used: `ClassicalMechanics.HarmonicOscillator` (ID 385205), `AmplitudePhase` (385330), `ω` (385208), `period` (385345), `Dimensionful` (394284), `WithDim` (394425), `UnitChoices.SI` (394270), `HasDerivAt` (124761), and `IsGreatest` (279653). The sources confirm `ω = sqrt (k/m)`, `period = 2*pi/ω`, the cosine amplitude-phase convention, coherent SI unit choices, and the intended derivative/greatest-element predicates.

## Physlib/Mathlib names grounded

- Physlib mechanics: `ClassicalMechanics.HarmonicOscillator`, `ClassicalMechanics.HarmonicOscillator.AmplitudePhase`, `ClassicalMechanics.HarmonicOscillator.ω`, and `ClassicalMechanics.HarmonicOscillator.period`.
- Physlib units: `Dimensionful`, `WithDim`, `M𝓭`, `L𝓭`, `T𝓭`, `UnitChoices.SI`, and the `MassUnit`/`LengthUnit`/`TimeUnit`-based SI system underlying those readouts.
- Mathlib analysis/order: `HasDerivAt`, `Real.cos`, `Real.pi`, `Set.Icc`, `Set.range`, `IsGreatest`, `NNReal`, and real absolute value.

## Local abstractions introduced

- Dimensionful aliases distinguish moment of inertia, torque magnitude, torsion constant, duration, and signed angular velocity while retaining Physlib dimensions. They are not scalar aliases.
- `TorsionPendulumApparatus` and `SuppliedFigure` preserve the verbal geometry, graph panels, labels, markers, and figure data channels.
- `TorsionPendulumSetup` keeps physical quantities and response functions independent of the answer.
- The four assumption structures separate textual data, primary-image readouts, positivity, and governing physics instead of bundling the target into a `ValidPhysics` premise.
- The scalar Physlib oscillator is used only as a one-coordinate mathematical oscillator. Explicit equations map its `m`-slot to rotational inertia and its `k`-slot to torsion stiffness, preventing those translational field names from silently changing the physical model.

## Grounding gaps

- LeanExplore found no torsion-pendulum-specific Physlib structure combining dimensionful moment of inertia, torsion constant, angular displacement, and angular velocity. The file therefore introduces a unit-aware local torsion-pendulum interface and bridges it explicitly to the grounded scalar harmonic-oscillator API.
- The `archon` executable was not available on `PATH`, so the optional read-only dependency-graph query could not be run. The blueprint chapter itself lists no dependency declarations.
- `.archon/AGENTS.md` was absent in the supplied project state; the stage-specific `.archon/prover-modes/physics-formalize.md` and the user-provided role instructions were followed.

No blueprint redraft is requested.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0278.lean` exits successfully. The only diagnostic is the expected `declaration uses sorry` warning for the autoformalization target.
