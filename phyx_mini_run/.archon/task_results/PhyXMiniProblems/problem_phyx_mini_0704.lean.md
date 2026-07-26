# Autoformalization result: `problem_phyx_mini_0704.lean`

## Assumption/target split

### Governing laws

- The fixed rotation axis passes through the central hub and the midpoint of the idealized propeller.
- The propeller is modeled as a uniform slender rod, so its axial inertia has the SI-readout relation `I = M * L^2 / 12`.
- The engine torque is constant and unopposed during startup, and fixed-axis rotational dynamics obey `tau = I * alpha`.
- The propeller starts from rest and obeys constant-angular-acceleration kinematics `omega_f = omega_i + alpha * t`.
- The rpm conversion uses dimensionless radians and one revolution equal to `2 * Real.pi` radians.

### Previous-part results

- None. The source report's `previous_parts` array is empty, and the blueprint presents a standalone question.

### Figure/data readouts

- Problem data: engine torque `60 N m` and target angular speed `200 rpm`.
- Primary-image scalar labels: total tip-to-tip length `L = 2.0 m` and mass `M = 40 kg`.
- Primary-image geometry and annotations: a two-bladed propeller and central hub, a tip-to-tip length arrow, the axis through the hub, a rotation-direction arrow, the engine-torque annotation, and the printed axis/mass/length labels.
- `MatchesSourceFigure` also requires the image's mass and length readouts to agree with the corresponding dimensionful setup quantities.

### Current target conclusions

- `timeInSeconds setup.startupDuration = 40 * Real.pi / 27`.
- The exact duration is within `0.1 s` of option C's displayed `4.6 s`.
- Option C is strictly closer to the exact duration than each other displayed option.

## Goal-faithfulness audit

The duration formula, the `0.1 s` approximation claim, and the unique selection of C occur only in the conclusion of `propeller_startup_duration_and_answer_choice`. They do not occur in `MatchesProblemData`, `MatchesSourceFigure`, or `ValidPropellerStartupPhysics`.

`startupDuration` is an independent `TimeQuantity`; it is not defined as `40 * Real.pi / 27`. The governing-law interface constrains it only through the general kinematic equation. Likewise, `AnswerChoice.durationSeconds` records all four printed choices without selecting C. Deriving the theorem therefore requires combining the source values, figure values, inertia law, torque law, rpm conversion, and kinematics.

The seven basic physical roles are not scalar aliases: each is a Physlib `Dimensionful (WithDim d NNReal)` at its appropriate physical dimension. Real values occur only as coherent SI readouts, angular/rpm readouts, exact dimensionless constants, or printed answer values.

## Declarations and blueprint correspondence

- Dimensionful roles: `MassQuantity`, `LengthQuantity`, `TimeQuantity`, `TorqueMagnitudeQuantity`, `MomentOfInertiaQuantity`, `AngularSpeedQuantity`, and `AngularAccelerationQuantity`.
- Readouts and conversion: `nonnegativeSIReadout`, the seven named SI readouts, and `angularSpeedInRevolutionsPerMinute`.
- Figure model: `FigureObject`, `FigureTextLabel`, `FigurePoint`, `PropellerFigureReadout`, and `MatchesSourceFigure`.
- Physical setup/model vocabulary: `RotationAxisPlacement`, `PropellerMassModel`, `StartupTorqueRegime`, and `PropellerStartupSetup`.
- Assumption interfaces: `MatchesProblemData` and `ValidPropellerStartupPhysics`.
- Answer data: `AnswerChoice` and `AnswerChoice.durationSeconds`.
- Blueprint label `thm:physics:phyx_mini_0704:target`: `PhyXMiniProblems.ProblemPhyXMini0704.propeller_startup_duration_and_answer_choice`.

The chapter exists and contains `% archon:physics`. The target declaration is ready for a statement-level `\leanok`, but the chapter was not edited because this prover's write permissions explicitly forbid blueprint edits.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical quantities SI units mass length time torque angular velocity` returned and grounded `Dimensionful`, `Dimension`, and `UnitChoices.SI`; it also exposed `RigidBodyMotion.angularVelocity` for comparison.
- `Dimensionful WithDim UnitChoices.SI` confirmed the core dimensionful API.
- `WithDim` returned the exact `WithDim` structure.
- `moment of inertia of a uniform slender rod about its midpoint` returned general rigid-body inertia declarations but no uniform-slender-rod midpoint formula.
- `rotational second law torque equals moment of inertia times angular acceleration` returned `RigidBody.rotational_equation_inertial`, `RigidBody.euler_equations`, and related declarations. The inspected `RigidBody.rotational_equation_inertial` is an `informal_lemma`, not a reusable theorem for this scalar setup.
- `angular velocity angular acceleration rigid body` and `constant angular acceleration kinematics final angular speed initial angular speed time` returned general three-dimensional rigid-body angular-velocity declarations but no matching scalar startup law.
- `Real.pi` returned the exact `Real.pi` declaration used in the rpm conversion and conclusion.

Source and module lookups were fetched for the candidates used or specifically assessed:

- `Dimensionful` and `UnitChoices.SI`: `Physlib.Units.Basic`.
- `WithDim`: `Physlib.Units.WithDim.Basic`.
- `Real.pi`: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
- Near misses `RigidBody.rotational_equation_inertial`: `Physlib.ClassicalMechanics.RigidBody.Basic`; `RigidBodyMotion.angularVelocity`: `Physlib.ClassicalMechanics.RigidBody.AngularVelocity`.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `WithDim`, `Dimensionful`, `UnitChoices`, and `UnitChoices.SI`.
- Mathlib: `NNReal`, `Real.pi`, and real `abs`/arithmetic notation.
- Lean LSP local search independently located `Dimensionful` and `WithDim` in the imported Physlib modules. The concrete names and elaborated signatures were validated by LSP diagnostics and `lake env lean`.

## Local abstractions introduced

- The quantity aliases specialize Physlib's actual dimensional types to nonnegative physical magnitudes; they preserve mass/length/time exponents rather than collapsing quantities to `ℝ`.
- Named scalar readout functions make the unit meaning of every real equation explicit.
- `PropellerFigureReadout` and the finite figure vocabularies retain the source image's objects, labels, incidence data, and tip-to-tip interpretation.
- `MatchesProblemData` and `MatchesSourceFigure` separate text inputs and image readouts from governing laws.
- `ValidPropellerStartupPhysics` is the smallest local one-axis law interface needed here: it states the uniform-rod inertia model, fixed-axis torque law, rest condition, and constant-acceleration kinematics, without containing the requested duration.
- `angularSpeedInRevolutionsPerMinute` is local because radians/revolutions are dimensionless angular conventions attached to the inverse-time readout.

## Source/law/answer audit

- Source: `60 N m`, `200 rpm`, image labels `2.0 m` and `40 kg`, and the central-hub/tip-to-tip geometry are represented explicitly.
- Laws/model: uniform-rod midpoint inertia, unopposed constant torque, `tau = I * alpha`, rest initial state, and `omega_f = omega_i + alpha * t` are assumptions rather than hidden definitions.
- Answer: these inputs imply `I = 40/3 kg m^2`, `alpha = 9/2 rad/s^2`, `omega_f = 20*pi/3 rad/s`, and hence `t = 40*pi/27 s`, approximately `4.65 s`; this supports recorded option C (`4.6 s`). The Lean target retains the exact value and the unique-closest-choice relation.

## Grounding gaps

- No directly reusable Physlib theorem was found for the midpoint inertia of a uniform slender rod, this scalar fixed-axis torque law, constant-angular-acceleration startup kinematics, or rpm conversion. The local abstractions above state those physical relations directly.
- The requested `.archon/AGENTS.md` is absent. The supplied role prompt, `.archon/PROGRESS.md`, and `.archon/prover-modes/physics-formalize.md` were followed; the archived project copy was consulted only to recover the general prover-role conventions.
- The runtime note said `archon` was on `PATH`, but `command -v archon` and the requested DAG query failed with `command not found`. The source report confirms there are no previous-part dependencies.
- No blueprint redraft is requested.

## Verification

- Lean LSP diagnostics: no errors and exactly one expected `declaration uses sorry` warning at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0704.lean`: exit code 0 with only that expected warning.
