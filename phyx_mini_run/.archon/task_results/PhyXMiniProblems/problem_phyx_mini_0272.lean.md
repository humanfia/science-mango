# Autoformalization result: `problem_phyx_mini_0272.lean`

## Assumption/target split

### Governing laws

- Thin-hoop inertia: `I = m R²` in every coherent unit system.
- Linearized spoke-end kinematics: for dimensionless angle `θ`, the signed tangential spring extension is `x = r θ`.
- Hooke restoring force: `F = -k x`.
- Tangential lever-arm torque: `τ = r F`, hence `τ = -κ θ` with `κ = k r²`.
- Rotational normal-mode balance: `I ω² = κ`.
- Strict positivity of `m`, `R`, `r`, `k`, `I`, `κ`, and `ω` selects the positive square-root branch and rules out cancellation by zero radii or mass.

### Previous-part results

- None. The source report has an empty `previous_parts` array.

### Figure/data readouts

- The primary bitmap shows a fixed wall on the left, a horizontal spring, a spoke and rim, and a fixed central axle about which the wheel may rotate.
- The spring is attached to the spoke at a point above the axle; its equilibrium force is tangential.
- `k` labels the spring, `r` labels the axle-to-attachment distance, and `R` labels the axle-to-rim radius.
- The curved arrow beneath the wheel indicates bidirectional rotation about the axle.
- The wheel is modeled as a thin hoop of mass `m` and radius `R`.
- The requested special case is the geometric datum `r = R`.
- No numerical scale is inferred from the bitmap.

### Current target conclusions

- For every coherent unit choice, `ω = Real.sqrt (k / m)` after imposing `r = R`.
- The modeled angular frequency therefore matches displayed answer choice C.

## Goal-faithfulness audit

The setup stores the angular frequency, inertia, and restoring coefficient as independent dimensionful fields. None is defined by the answer formula. `MatchesProblemAndSuppliedFigure` supplies only qualitative figure facts, the thin-hoop/fixed-axle/small-angle model choices, and the geometric condition `r = R`; it contains no frequency equation. `HasPhysicalHoopSpringParameters` contains positivity only. `SatisfiesLinearizedHoopSpringLaws` contains the unsimplified general laws `I = m R²`, `κ = k r²`, and `I ω² = κ`, together with the displacement/force/torque route that physically justifies `κ`; it neither assumes `r = R` nor states `ω = sqrt (k/m)`. The squared-frequency simplification is a lemma conclusion, and the positive-root formula and choice C occur only in the final theorem conclusion. The displayed-choice definition is answer-list metadata and is never assumed to equal the modeled frequency.

## Declarations and blueprint labels

- `HoopSpringSetup`: independent physical quantities, signed linearized observables, and qualitative model roles.
- `WheelSpringFigure`, `FigureFeature`, `FigureLabel`, `HorizontalSide`, `FigureOrientation`, `RotationArrow`: primary-image transcription.
- `MatchesProblemAndSuppliedFigure`: problem statement, image readout, thin-hoop/fixed-axle assumptions, and special case `r = R`.
- `HasPhysicalHoopSpringParameters`: strict physical positivity.
- `SatisfiesLinearizedHoopSpringLaws`: hoop inertia, small-angle kinematics, Hooke force, torque, restoring coefficient, and normal-mode balance.
- `angularFrequencySquared_eq_springConstant_div_mass`: derived intermediate relation `ω² = k/m`.
- `AnswerChoice`, `displayedAngularFrequencyReadout`, `recordedDatasetAnswerChoice`, `MatchesAnswerChoice`: faithful answer-choice metadata.
- `hoopSpringAngularFrequency_when_attachmentAtRim`: formalizes `thm:physics:phyx_mini_0272:target`.

## LeanExplore queries/candidates actually used

- Query `moment of inertia of a hoop rotating about a fixed axle` found `RigidBody.inertiaTensor`, `RigidBody.angularMomentum`, `RigidBody.rotational_equation_inertial`, and related rigid-body declarations. No candidate directly states the scalar thin-hoop inertia law or this spoke-spring reduction.
- Query `small angle rotational oscillator spring torque angular frequency` found `ClassicalMechanics.HarmonicOscillator.ω`, `ClassicalMechanics.HarmonicOscillator.ω_sq`, `RigidBody.rotational_equation_inertial`, and `RigidBody.small_oscillations_about_equilibrium`.
- Query `ClassicalMechanics.HarmonicOscillator.ω` confirmed that PhysLean's translational oscillator defines `ω = sqrt (k/m)` and supplies `ω_sq`, but its structure fields are explicitly a physical mass and linear spring constant. It was not repurposed with a moment of inertia masquerading as mass.
- Query `Real.sqrt` found and grounded `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt`; this is used for the positive angular-frequency formula and displayed choices.
- Queries `SI units mass length spring constant moment of inertia angular frequency`, `Dimensionful WithDim UnitChoices.SI`, and `WithDim` grounded the dimensionful representation used here.
- Preflight queries recorded in `.archon/task_results/physics-grounding-PhyXMiniProblems_problem_phyx_mini_0272.md` were also reviewed.

## PhysLean/Mathlib names grounded

- `Dimensionful` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- `Dimension`, `M𝓭`, `L𝓭`, and `T𝓭` through `Physlib.Units.WithDim.Basic`.
- `UnitChoices` and `UnitChoices.SI` from `Physlib.Units.Basic` (the formalization quantifies over arbitrary coherent `UnitChoices`).
- `Real.sqrt` from `Mathlib.Analysis.Real.Sqrt`.
- `ClassicalMechanics.HarmonicOscillator`, `.ω`, and `.ω_sq` were inspected as near matches but intentionally not used because their documented fields have translational rather than rotational physical roles.

## Local abstractions introduced

- Dimensionful aliases for mass, length, spring stiffness, axial moment of inertia, restoring-torque coefficient, angular frequency, signed extension, signed force, and signed torque. These are aliases of PhysLean's genuine unit-independent `Dimensionful (WithDim ...)` representation, not scalar aliases or one-field scalar wrappers.
- `WheelSpringFigure` preserves the qualitative figure geometry and label ownership without inventing numerical pixel-derived data.
- `SatisfiesLinearizedHoopSpringLaws` is the smallest local governing-law interface that preserves the rotational mechanics absent from the located APIs. It exposes the general physical chain from spoke displacement to torque and normal-mode balance rather than embedding the requested answer.

## Grounding gaps

- LeanExplore did not locate a ready-made scalar moment-of-inertia theorem for a thin hoop or a ready-made rotational oscillator specialized to a spring attached to a spoke. The local laws therefore state `I = mR²`, `κ = kr²`, and `Iω² = κ` explicitly.
- The advertised `archon` executable was not on `PATH`, so `archon dag-query ancestors --node thm:physics:phyx_mini_0272:target --json` could not be run. The source report independently confirms there are no previous parts.
- The requested `.archon/AGENTS.md` file is absent. The complete `.archon/prover-modes/physics-formalize.md` instructions were used instead.
- The blueprint theorem environment was not edited to add `\\leanok`, because the task's explicit write permissions prohibit editing blueprint chapters. The plan/dispatcher agent should add that marker after accepting this declaration.

## Redraft requests

- None for the physical statement. The blueprint is sufficient for this formalization.

## Verification

- `archon-lean-lsp` reported exactly two expected `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0272.lean` exited successfully with the same two expected warnings, one for the derived squared-frequency lemma and one for the final theorem.
- `git diff --check` reported no whitespace errors for the two authorized output paths.
