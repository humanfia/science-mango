# Autoformalization result: `problem_phyx_mini_0279.lean`

The chapter contains `% archon:physics`, so the physics-formalize discipline
applies. The requested `.archon/AGENTS.md` is absent in this checkout; I used
the available `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`,
the iteration-002 objectives and plan, and the exact review-gate reason. There
was no file-specific `/- USER: ... -/` comment. The iteration-001 model was
retained and an explicit `import Mathlib` was added to repair the exact gate
failure that the physics target did not import Mathlib.

## Assumption/target split

### Governing laws

- The effective one-coordinate Physlib harmonic oscillator has mass parameter
  `M + I/R^2` and stiffness parameter equal to the spring stiffness.
- Its displacement coordinate agrees with the spring extension, and its
  `potentialEnergy` agrees with the physical spring-energy SI readout.
- The Physlib `RigidBody 3` mass and axial inertia-tensor entry agree with the
  cylinder mass and axial moment of inertia; its angular-velocity vector lies
  along the chosen rolling axis.
- The solid-cylinder inertia law is `I = (1/2) M R^2`.
- Translational kinetic energy is `(1/2) M v^2`.
- Physical rotational kinetic energy agrees with
  `RigidBody.rotationalKineticEnergy`.
- Rolling without slipping obeys `v = R omega` at both modeled events.
- Spring, translational, and rotational mechanical energy is conserved from
  release to the equilibrium passage.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- The primary image shows a solid orange cylinder, its axle, a spring, a
  vertical wall, and a horizontal supporting surface.
- The label `M` refers to the cylinder, while `k` refers to the spring.
- The horizontal spring joins the axle to the wall anchor; the cylinder lies
  left of the wall and touches the horizontal support.
- The primary image's curved arrow is clockwise: at the left side of the
  cylinder its arrowhead points upward. This primary readout takes precedence
  over the auxiliary caption's counterclockwise description.
- The spring-stiffness readout is exactly `3 N/m`, the release extension is
  exactly `1/4 m`, and the equilibrium extension is zero.
- The cylinder is released from rest, so both its center-of-mass speed and
  angular-speed readouts vanish at release.
- The cylinder is solid, the contact regime is rolling without slip, and the
  mass, radius, stiffness, and initial extension are positive.

### Current target conclusions

- The initially stretched spring stores `3/32 J`.
- The cylinder's rotational kinetic energy at equilibrium is one third of
  that initial spring energy.
- Therefore the equilibrium rotational kinetic energy is exactly `1/32 J`,
  i.e. `0.03125 J`.
- The resulting physical energy matches displayed answer choice D.

## Goal-faithfulness audit

The setup stores spring, translational, and rotational energies as independent
dimensionful physical quantities indexed by motion event. None is defined from
`1/32`, `0.03125`, or an answer choice. The problem-data, figure-data,
positivity, and governing-law structures contain neither the requested
equilibrium rotational-energy value nor the one-third energy partition.

The answer table is metadata only. `MatchesDisplayedEnergy` compares an
independent physical energy's SI readout with a displayed choice; it does not
define that physical energy. The current conclusion requires combining the
Hooke-energy law, release and equilibrium data, solid-cylinder inertia,
no-slip kinematics, both kinetic-energy laws, and conservation. Thus no target
conclusion is smuggled into a premise or discharged by unfolding a local
definition.

## Declarations and blueprint correspondence

- Dimensionful roles and coherent-SI projections: `MassQuantity`,
  `LengthQuantity`, `SpeedQuantity`, `AngularSpeedQuantity`,
  `SpringConstantQuantity`, `MomentOfInertiaQuantity`, `EnergyQuantity`, and
  their named readout functions.
- Event and image vocabulary: `MotionEvent`, `FigureObject`, `FigureLabel`,
  `SpringEndpoint`, `Orientation`, `RotationSense`, `CylinderShape`,
  `SurfaceContact`, and `ReleaseProtocol`.
- Physical and evidential interfaces: `RollingCylinderFigure`,
  `RollingCylinderSpringSetup`, `MatchesPrimaryFigure`, `MatchesProblemData`,
  `HasPhysicalParameters`, and `SatisfiesRollingCylinderSpringLaws`.
- Derived statements:
  `initialSpringPotentialEnergy_eq_three_over_thirtyTwo` and
  `rotationalKineticEnergy_is_oneThird_initialSpringEnergy`.
- Answer metadata: `AnswerChoice`, `AnswerChoice.joules`,
  `recordedAnswerChoice`, and `MatchesDisplayedEnergy`.
- `rotationalKineticEnergyAtEquilibrium_eq_one_over_thirtyTwo` and
  `rotationalKineticEnergyAtEquilibrium_matches_answerD` formalize blueprint
  label `thm:physics:phyx_mini_0279:target`.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `spring harmonic oscillator potential energy` and
  likely-name query
  `ClassicalMechanics.HarmonicOscillator.potentialEnergy` both returned the
  used `ClassicalMechanics.HarmonicOscillator.potentialEnergy` declaration.
- Natural-language query
  `rigid body rotational kinetic energy inertia tensor angular velocity` and
  likely-name query `RigidBody.rotationalKineticEnergy` returned the used
  `RigidBody.rotationalKineticEnergy` declaration and its related inertia API.
- Query `dimensionful physical energy speed SI units` returned the used
  `Dimensionful` and `UnitChoices.SI` declarations.

Source, module, and docstring information was fetched only for the candidates
used directly: `ClassicalMechanics.HarmonicOscillator.potentialEnergy`,
`RigidBody.rotationalKineticEnergy`, `Dimensionful`, and `UnitChoices.SI`.

## Physlib/Mathlib names grounded

- `ClassicalMechanics.HarmonicOscillator.potentialEnergy` from
  `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` is defined as the
  oscillator potential `1/2 k <x,x>`.
- `RigidBody.rotationalKineticEnergy` from
  `Physlib.ClassicalMechanics.RigidBody.KineticEnergy` is defined as one half
  the contraction of angular velocity with the inertia tensor.
- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic` provide
  unit-independent physical quantities and coherent SI evaluation.
- `DimSpeed` and `DimEnergy` are the Physlib dimensionful speed and energy
  types imported from `Physlib.Units.WithDim.Speed` and `.Energy`.
- `WithDim`, `M𝓭`, `L𝓭`, and `T𝓭` preserve the mass, length, time, and compound
  dimensions of all remaining physical quantities.
- The file now imports `Mathlib` explicitly, as required by the retry gate;
  `EuclideanSpace`, `Fin`, `NNReal`, and real arithmetic are Mathlib APIs used
  by the model and by the grounded Physlib interfaces.

## Local abstractions introduced

- `RollingCylinderSpringSetup` is the smallest local apparatus interface that
  keeps the dimensionful physical quantities, the two motion events, the
  Physlib oscillator, and the three-dimensional rigid body distinct.
- `RollingCylinderFigure` and the figure enums preserve the image's objects,
  labels, attachment endpoints, orientations, contact, relative position, and
  rotation sense without inventing scalar geometry.
- The data, positivity, figure, and law predicates are separate so that source
  observations and governing physics cannot be confused with the requested
  answer.
- The scalar SI bridges are explicitly named projections of dimensionful
  quantities, not replacements for the physical primitives.

## Grounding gaps and redraft requests

- LeanExplore exposed the generic Physlib oscillator and rigid-body energy
  APIs, but no single ready-made Physlib object for a spring-driven cylinder
  rolling without slip. The local setup and law interface preserves this
  coupled physical role while reusing the available library definitions.
- `.archon/AGENTS.md` is missing. The iteration review says an identical-SHA
  canonical copy was used by orchestration; this lane followed the available
  stage-mode instructions instead.
- The optional read-only dependency-graph query could not be run because the
  `archon` executable is not available on `PATH` in this environment. The
  blueprint chapter declares no explicit dependency nodes.
- The blueprint was not edited to add `\leanok`, because the task's explicit
  write permissions prohibit editing blueprint chapters. An authorized
  orchestration step should add the marker after accepting the declarations.

No blueprint-content redraft is otherwise requested.

## Verification

- `archon-lean-lsp` reports no errors or failed dependencies and exactly four
  expected `declaration uses sorry` warnings, one for each by-sorry derived
  lemma/theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0279.lean` exits with code
  0 and the same four expected warnings.
