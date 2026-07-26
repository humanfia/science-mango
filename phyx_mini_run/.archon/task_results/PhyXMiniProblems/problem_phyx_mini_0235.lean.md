# Autoformalization result: `problem_phyx_mini_0235.lean`

## Assumption/target split

### Governing laws

- `HasPhysicalParameters` requires positive spring stiffness, hanging mass,
  gravitational acceleration, equilibrium extension, and both pulley radii.
- `SatisfiesStaticEquilibrium.forceBalance` states the pre-displacement balance
  `k x_eq = m g`; gravity sets equilibrium but is not inserted into the
  oscillation answer.
- `SatisfiesNoSlipKinematics.rimVelocity` states `v = R Omega` for every
  nonnegative pulley-mass readout, radius stage, and time.
- `SatisfiesSolidDiskMomentOfInertia.inertiaLaw` states the general solid-disk
  law `I = (1/2) M R^2` at both radius stages.
- `SatisfiesSmallOscillationReduction` states the Newton--Euler effective-mass
  reduction `m_eff = m + I/R^2` and preserves the original spring constant.
  The resulting mode is PhysLean's `ClassicalMechanics.HarmonicOscillator`,
  whose general angular-frequency definition is `sqrt (k / m_eff)`.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemReadouts` records `k = 100 N/m`, `m = 200 g = 0.2 kg`,
  the original radius `2.00 cm = 0.02 m`, and the doubled radius
  `4.00 cm = 0.04 m`.
- `SatisfiesRadiusDoubling` separately records that the final radius is twice
  the original radius.
- The primary image shows a horizontal spring fixed to the left wall, a
  horizontal string segment passing over the pulley, a vertical segment
  supporting `m`, and the hanging object below the pulley.
- The primary image resolves the auxiliary-caption ambiguity: `M` labels the
  pulley disk, `R` labels its radius, `k` labels the spring, and `m` labels the
  hanging object. There is no separate block of mass `M`.
- The prose idealizations are stored explicitly: light spring and string,
  solid-disk pulley, fixed smooth axle, free rotation, no slip, small
  oscillation about equilibrium, and pull-down/release preparation.
- `displayedAngularFrequency_rad_per_s` transcribes the four printed answer
  values, while `recordedDatasetAnswer = D` records source metadata only.

### Current target conclusions

- `solidDisk_effectiveRotationalMass` derives `I/R^2 = M/2`, rather than
  assuming the cancellation of radius.
- `angularFrequency_squared` derives
  `omega^2 = k / (m + M/2)` from the independent inertia and reduction laws.
- `angularFrequency_independent_of_radiusDoubling` derives that changing the
  radius of the same solid disk does not change the angular frequency.
- `problem_phyx_mini_0235` proves that, over nonnegative symbolic pulley-mass
  readouts (including the ideal zero-inertia endpoint), the greatest final
  angular frequency is `sqrt 500 rad/s`; it rounds to `22.4 rad/s` and makes D
  the unique closest displayed choice.

## Goal-faithfulness audit

No premise mentions `sqrt 500`, `22.4`, choice D, a greatest-frequency set, or
the final bound. `SpringPulleyOscillator.effectiveOscillator` is independent
data constrained only by the general effective-mass and spring-constant laws.
`SatisfiesSmallOscillationReduction` is uniform in the pulley mass and radius
stage and contains neither the problem's numeric readouts nor an extremal
claim. The radius cancellation and the frequency formula remain conclusions
of separate lemmas.

`recordedDatasetAnswer` and the displayed-choice table are closed metadata
definitions and are not theorem hypotheses. `RoundsToDisplayedTenth` and
`IsUniqueClosestDisplayedChoice` merely define how a derived exact frequency
is compared with the printed choices; neither makes D true by unfolding.
There are no `True` placeholders, reflexive targets, scalar aliases for
physical primitives, or local definitions of the requested extremum.

The interpretation of “highest possible” is made explicit: the otherwise
unspecified `M` ranges over nonnegative SI mass readouts, so the ideal `M = 0`
endpoint attains the upper value. This interpretation is visible in the
conclusion's set and is not hidden in a premise.

## Declarations created and blueprint correspondence

- Figure and model vocabularies: `RadiusStage`, `StringSegment`,
  `Orientation`, `FigureObject`, `FigureLabel`, `MassIdealization`,
  `PulleyShape`, `AxleCondition`, `PulleyFreedom`, `StringPulleyContact`,
  `OscillationRegime`, and `ReleaseProtocol`.
- Physical/figure records: `SpringPulleyFigure` and
  `SpringPulleyOscillator`. Real-valued physical fields are explicitly named
  SI readouts; the effective mode uses PhysLean's oscillator structure.
- Data and scenario interfaces: `MatchesProblemReadouts`,
  `MatchesScenarioAndSuppliedFigure`, and `HasPhysicalParameters`.
- Governing-law interfaces: `SatisfiesRadiusDoubling`,
  `SatisfiesStaticEquilibrium`, `SatisfiesNoSlipKinematics`,
  `SatisfiesSolidDiskMomentOfInertia`, and
  `SatisfiesSmallOscillationReduction`.
- Derived declarations: `solidDisk_effectiveRotationalMass`,
  `angularFrequency_squared`, and
  `angularFrequency_independent_of_radiusDoubling`.
- Answer modeling: `AnswerChoice`,
  `displayedAngularFrequency_rad_per_s`, `recordedDatasetAnswer`,
  `RoundsToDisplayedTenth`, and `IsUniqueClosestDisplayedChoice`.
- `PhyXMiniProblems.ProblemPhyXMini0235.problem_phyx_mini_0235` corresponds
  to blueprint label `thm:physics:phyx_mini_0235:target`.

## LeanExplore queries/candidates actually used

Every search used `packages: ["Mathlib", "Physlib"]`.

- `solid disk moment of inertia pulley no slip spring mass angular frequency effective mass`
  found `ClassicalMechanics.HarmonicOscillator.ω` (ID 385208) and its
  square-frequency lemma (ID 385210), but only solid-sphere rigid-body inertia
  specializations.
- `ClassicalMechanics.HarmonicOscillator.ω` and
  `structure ClassicalMechanics.HarmonicOscillator mass spring constant`
  found the exact structure (ID 385205), angular-frequency definition
  (ID 385208), and `ω_sq` lemma (ID 385210). Source, module, and docstring
  were fetched for these candidates before use.
- `SI units mass length time angular frequency spring constant moment of inertia`
  and `MassUnit.kilograms LengthUnit.meters dimensional quantity SI value`
  found `UnitChoices.SI` (ID 394270), `WithDim.scaleUnit_val`, and
  `UnitExamples.meters400` (ID 394339). The unit API was inspected, but the
  scalar PhysLean oscillator API made explicitly named SI readouts the
  smaller compatible interface for this file.
- `moment of inertia solid disk cylinder RigidBody` found
  `RigidBody.inertiaTensor` and `RigidBody.solidSphere_inertiaTensor`, but no
  solid-disk/cylinder specialization.
- `Real.sqrt` selected Mathlib's `Real.sqrt` (ID 143113); its source, module,
  and docstring were fetched.
- `IsGreatest greatest element of a set` selected `IsGreatest` (ID 279653)
  from `Mathlib.Order.Bounds.Defs`; its source, module, and docstring were
  fetched.

## PhysLean/Mathlib names grounded

- `ClassicalMechanics.HarmonicOscillator`
- `ClassicalMechanics.HarmonicOscillator.ω`
- `ClassicalMechanics.HarmonicOscillator.ω_sq`
- `Real.sqrt`
- `IsGreatest`

## Local abstractions introduced

- `SpringPulleyOscillator` is a multi-field apparatus model. Its real fields
  are explicitly SI scalar readouts (`_kg`, `_m`, `_N_per_m`, and so on), not
  aliases identifying a physical primitive with `Real`.
- `SpringPulleyFigure` and the accompanying enums preserve the actual figure
  labels, incidences, attachments, and orientations without extracting fake
  numerical information from pixels.
- Local law structures were required for the no-slip kinematics, solid-disk
  scalar moment of inertia, static equilibrium, and pulley effective-mass
  reduction. Each states a standard governing relation and none states the
  requested numeric extremum.
- The answer-choice and rounding predicates distinguish the exact physical
  value `sqrt 500` from the displayed one-decimal readout `22.4`.

## Grounding gaps and redraft requests

- LeanExplore exposed a general rigid-body inertia tensor and a solid-sphere
  specialization, but no solid-disk pulley model, no no-slip string/pulley
  interface, and no ready-made spring--pulley effective-mass theorem. The
  faithful local governing-law interfaces above fill those gaps.
- `.archon/AGENTS.md` is absent. The available
  `.archon/prover-modes/physics-formalize.md` was read and followed as the role
  specification instead.
- The `archon` executable described for optional dependency-graph navigation
  was not available on `PATH`. The source report lists no previous parts, and
  the blueprint contains only this target, so this did not block the model.
- The assigned Lean file did not previously exist, so it contained no
  file-specific `/- USER: ... -/` hints.
- The blueprint's proof paragraph does not include the physical derivation;
  a future redraft could record `I = M R^2/2`, `m_eff = m + I/R^2`, and the
  resulting extremization explicitly.
- The blueprint environment still needs the Lean declaration link and
  `\leanok`. This task's explicit write permissions forbid editing blueprint
  chapters, so the plan/blueprint agent should add them to
  `thm:physics:phyx_mini_0235:target`.

## Verification

- `archon-lean-lsp` diagnostics report no errors and exactly four expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0235.lean` exits with
  status 0 and the same four expected warnings.
