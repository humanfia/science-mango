# Autoformalization result: `problem_phyx_mini_0787.lean`

## Assumption/target split

### Governing laws

- A basketball modeled as a thin hollow spherical shell has axial moment of
  inertia `I = (2/3) M R²`.
- Translational kinetic energy is `M v² / 2`.
- Rotational kinetic energy is `I ω² / 2`; the modeled energy is also tied to
  Physlib's `RigidBody.rotationalKineticEnergy` using an SI-coordinate angular
  velocity vector and the matching axial inertia-tensor entry.
- Gravitational potential energy relative to the dashed valley datum is
  `M g h`.
- Total gravitational-plus-translational-plus-rotational mechanical energy is
  conserved at every modeled event.
- Rolling without slipping at the end of the rough part gives `v = R ω`.
- The smooth part exerts no tangential contact force, so angular speed is
  conserved between entry to the smooth part and the translational turning
  point.

### Previous-part results

- None.  The source report lists no previous parts.

### Figure/data readouts

- Image `787.png` shows the basketball at the upper left, a left slope labelled
  `Rough`, a right slope labelled `Smooth`, a valley bottom, an `H₀` vertical
  arrow, and a dashed valley datum.
- The arrow's upper endpoint is aligned with the initial center-of-mass level
  and its lower endpoint with the valley datum.
- The basketball is a hollow spherical shell, begins from both translational
  and rotational rest, and starts at center-of-mass height `H₀`.
- The rough-to-smooth transition is modeled at the valley datum.
- The named highest point on the smooth side is a translational turning point;
  its rotational speed is not assumed to vanish.
- The rough phase prevents slipping, the smooth phase has no tangential
  friction, and rolling resistance is neglected.

### Current target conclusions

- The center-of-mass height at the highest point on the smooth side is
  `(3/5) H₀`.
- This fraction is the displayed answer choice B; answer-choice data are kept
  as conclusion-side metadata and are not theorem premises.

## Goal-faithfulness audit

The unknown highest-point height is an independent value of
`RollingBasketballSetup.centerOfMassHeightAboveValleyDatum`; it is not defined
from `H₀`, `3/5`, an answer choice, or an energy formula.  No premise structure
contains the equality `h = (3/5) H₀`.  The setup also stores potential,
translational, and rotational energies independently, and the law structures
relate them only through standard general formulas and conservation laws.

`MatchesRollingBasketballProblemData` assumes zero translational speed at the
named highest point because this characterizes a turning point, but it assumes
neither that point's height nor its potential energy.  The smooth-side angular
speed conservation field is the standard no-tangential-torque phase law and
also contains no height relation.  The factor `3/5` first occurs in the
conclusion of a derived energy-partition lemma and in the final theorem; it is
absent from every setup field and assumption structure.

The recorded answer definition `recordedAnswerChoice := .B` is dataset
metadata only.  The final theorem states the physical height equality directly
and does not become true by unfolding that metadata.

## Declarations created and blueprint correspondence

- Dimensionful quantity/readout layer: `MassQuantity`, `LengthQuantity`,
  `SpeedQuantity`, `AngularSpeedQuantity`, `MomentOfInertiaQuantity`,
  `AccelerationQuantity`, `EnergyQuantity`, and coherent-SI readout functions.
- Physical/figure vocabulary: `MotionEvent`, `MotionPhase`, `SurfaceFinish`,
  `ContactRegime`, `BallShape`, `FigurePart`, `FigureLabel`, and
  `DepictedBallLocation`.
- Independent model: `BasketballValleyFigure` and `RollingBasketballSetup`.
- Assumption interfaces: `MatchesPrimaryBasketballValleyFigure`,
  `MatchesRollingBasketballProblemData`,
  `HasPhysicalRollingBasketballParameters`,
  `SatisfiesRollingBasketballEnergyLaws`, and
  `SatisfiesRoughAndSmoothContactLaws`.
- Internal derived lemmas (no separate blueprint labels):
  `translationalEnergyAtTransition_eq_threeFifths_initialPotentialEnergy` and
  `potentialEnergyAtHighestPoint_eq_transitionTranslationalEnergy`.
- Answer metadata: `AnswerChoice`, `AnswerChoice.heightFraction`, and
  `recordedAnswerChoice`.
- `problem_phyx_mini_0787` corresponds to blueprint label
  `thm:physics:phyx_mini_0787:target`.

## LeanExplore queries and candidates

All searches used package filters `Mathlib` and `Physlib`.

- Query: “moment of inertia hollow spherical shell rotational kinetic energy
  rolling without slipping”.  Used candidate
  `RigidBody.rotationalKineticEnergy` (id 385448); its source and module
  `Physlib.ClassicalMechanics.RigidBody.KineticEnergy` were fetched.
- Query: “kinetic energy rotational motion angular velocity moment of
  inertia”.  Inspected candidate
  `RigidBodyMotion.kineticEnergy_eq_translational_add_angularVelocity`
  (id 385455) and its source/module.  It is a full trajectory/integral theorem
  and was not used because this finite-event problem needs only an axial
  readout.
- Query: “physical dimensions mass length velocity energy gravitational
  acceleration”.  Used `Dimension` (id 394292); source and module
  `Physlib.Units.Dimension` were fetched.
- Query: “DimEnergy DimSpeed WithDim physical units”.  Used `DimEnergy`
  (id 394468) and `DimSpeed` (id 394481); source and modules were fetched.
- Queries: “hollow sphere thin spherical shell moment of inertia” and
  “RigidBody spherical shell inertiaTensor”.  The closest physics result was
  `RigidBody.solidSphere_inertiaTensor` (id 385484), which is the wrong mass
  distribution for a basketball.
- Query: “gravitational potential energy mass gravity height”.  No compatible
  general mechanics declaration was returned; `DimEnergy` was the useful
  dimensional candidate.
- Query: “mechanical energy conservation frictionless rolling”.  Returned
  oscillator- and free-particle-specific conservation theorems, not a general
  rough/smooth rolling theorem.

## Physlib/Mathlib names grounded

- `RigidBody`, `RigidBody.mass`, `RigidBody.inertiaTensor`, and
  `RigidBody.rotationalKineticEnergy` from Physlib's rigid-body API.
- `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`,
  `Dimensionful`, `WithDim`, `UnitChoices.SI`, `DimSpeed`, and `DimEnergy` from
  Physlib's units API.
- `NNReal` and ordinary real-number algebra from Mathlib, used only beneath the
  dimensionful wrappers or at coherent readout boundaries.

These names were accepted by `archon-lean-lsp` diagnostics and by a direct
Lean compile.

## Local abstractions introduced

- No Physlib declaration for a thin hollow spherical shell or its `2/3` axial
  inertia law was found.  `BallShape.thinHollowSphericalShell` and the general
  law field `hollowSphericalShellMomentOfInertia` preserve the correct mass
  distribution without pretending the available solid-sphere theorem applies.
- The event/phase/contact types distinguish release, the rough-to-smooth
  transition, the smooth-side turning point, no-slip rolling, and frictionless
  contact.  This preserves the essential fact that translation and rotation
  remain coupled only on the rough part.
- `BasketballValleyFigure` records semantic image evidence without inventing
  metric data from raster coordinates.
- The gravitational, mechanical-energy-conservation, and contact laws are
  explicit proposition-valued interfaces because no compatible general
  Physlib theorem was found.  They state standard governing physics, not the
  requested final height.
- All basic physical magnitudes use `Dimensionful (WithDim ...)` or existing
  `DimSpeed`/`DimEnergy`; no physical primitive was collapsed to a scalar
  alias.

## Grounding gaps

- Physlib currently exposes a solid-sphere inertia result but the search found
  no thin-hollow-spherical-shell constructor or inertia theorem.
- No general Physlib API matching uniform gravitational potential energy,
  rolling without slipping across a rough-to-smooth boundary, or mechanical
  energy conservation for this finite-event setup was found.
- The requested `archon dag-query` navigation could not be run because
  `archon` was not on `PATH` in this environment (`command not found`).

## Verification and workflow notes

- `archon-lean-lsp` reported success with exactly three expected “declaration
  uses `sorry`” warnings and no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0787.lean` exited with code
  0 and the same three expected warnings at the two derived lemmas and the main
  theorem.
- The assigned Lean file did not exist initially, so it was created and marked
  with a `/- USER: ... -/` provenance comment.
- `.archon/AGENTS.md` was absent.  The applicable role instructions were
  instead confirmed in `.archon/prover-modes/physics-formalize.md`.
- The blueprint chapter was not edited because the task's explicit write
  permissions allow edits only to the assigned Lean file and this result file.
  Consequently, the orchestrator or plan agent should add `\leanok` to the
  `thm:physics:phyx_mini_0787:target` environment.

## Redraft requests

- No mathematical redraft is requested.  The only follow-up is the permitted
  blueprint-status update (`\leanok`) noted above.
