# Autoformalization result (Archon iteration 003): `problem_phyx_mini_0712.lean`

The iteration-003 review found that the existing assigned Lean file already
implements the revised physics model faithfully. No semantic Lean change was
needed. This report is a genuine post-formalization audit tied to the source,
primary image, LeanExplore calls, LSP diagnostics, and compilation performed in
this iteration.

## Assumption/target split

### Governing laws

- `SatisfiesDiskAndLoopMomentOfInertiaLaws.solidDiskMomentOfInertia` states
  the uniform solid-disk axial law `I_disk = (1 / 2) M_disk R_disk^2`.
- `SatisfiesDiskAndLoopMomentOfInertiaLaws.thinLoopMomentOfInertia` states
  the thin circular-loop axial law `I_loop = M_loop R_loop^2`.
- `SatisfiesIsolatedFrictionalAngularMomentumLaw.initialAngularMomentumLaw`
  states that the initial total axial angular momentum is the sum of the two
  independently stored `I * omega` body contributions.
- `SatisfiesIsolatedFrictionalAngularMomentumLaw.finalAngularMomentumLaw`
  states that the final total is `(I_disk + I_loop) * omega_final` after the
  bodies share one independently stored final angular velocity.
- `SatisfiesIsolatedFrictionalAngularMomentumLaw.axialAngularMomentumConserved`
  states equality of the independently stored initial and final axial angular
  momenta. Internal friction and negligible external axial torque are recorded
  separately.
- `HasPhysicalDiskLoopParameters` gives positivity/nondegeneracy conditions.
  It contains no solved final angular velocity.

### Previous-part results

- None. The source report has `previous_parts: []`.
- No ancestor theorem is imported or assumed. The requested `archon dag-query`
  navigation was attempted in iteration 003, but the `archon` executable is not
  available on `PATH` in this runtime.

### Figure/data readouts

- The disk and loop each have diameter `20 cm = 1 / 5 m`, with radius half the
  diameter.
- The rotating body is a `2 kg` uniform solid disk. The dropped body is a
  `1 kg` thin circular loop.
- The disk initially rotates at `200 rpm`; the loop has zero initial axial
  spin. The prose is used here because the auxiliary generated caption's claim
  that the loop rotates conflicts with the prose and primary image.
- The loop is dropped straight down, friction acts during contact, and the two
  bodies rotate together afterward.
- `MatchesPrimaryDiskLoopFigure` records the before/after stages, both bodies,
  the loop above the disk before contact, the shared vertical symmetry axis,
  two downward drop arrows, rotation arrows, upward `L_i` and `L_f` arrows, all
  printed labels, and the loop riding on the disk afterward. Its drawing
  coordinate is explicitly schematic and is not a physical length.
- `AnswerChoice.revolutionsPerMinute` records displayed options A `122`, B
  `88`, C `100`, and D `134` rpm. `recordedDatasetAnswer := .C` is answer
  metadata, not a physical premise.

### Current target conclusions

- `diskMomentOfInertia_equals_loopMomentOfInertia` derives equality of the two
  axial inertia readouts from the data and shape laws.
- `finalCommonAngularVelocity_formula` derives the common final axial angular
  velocity by solving the conservation equation.
- `finalAngularVelocity_is_100_rpm` concludes that the final common angular
  velocity is `100 rpm`, matches recorded choice C, and matches no other
  displayed choice.

## Goal-faithfulness audit

The substantive conclusions—equal inertias, the solved quotient formula,
`100 rpm`, satisfaction of choice C, and uniqueness of C—occur only in lemma or
theorem conclusions. They do not occur in `DiskLoopRotationSetup`, any
`Matches...`/`HasPhysical...` premise, either governing-law structure, or a
definition that makes the result true by unfolding.

In particular, `DiskLoopRotationSetup.finalCommonAngularVelocity` is an
independently stored dimensionful observable. The initial and final angular
momenta are also stored independently. The law structures relate those values
through standard inertia formulas, `L = I omega`, and conservation; none
contains `100 rpm` or an answer label. `MatchesAnswerChoice` only compares an
independent rpm readout to source metadata. Unfolding `recordedDatasetAnswer`
or the option table cannot prove that the physical observable has that value.

Physical primitives are not transparent scalar aliases. Length, mass, axial
angular velocity, axial moment of inertia, and axial angular momentum specialize
Physlib's unit-independent `Dimensionful (WithDim ...)` representation. Real
numbers are used only for named SI/rpm projections, schematic drawing
coordinates, and displayed option values.

## Source/law/answer audit

- **Source evidence:** `reports/phyx_mini/problem_phyx_mini_0712.source.json`
  and primary image `phyx_data/test_image/712.png` were inspected in iteration
  003. The prose says the disk rotates; the image draws the rotational arrow on
  the disk and places `omega_i = 200 rpm` on the common before-stage axis. This
  outweighs the contradictory auxiliary caption sentence about the loop.
- **Governing laws:** the model uses only the two standard axial shape-inertia
  laws, before/after `L = I omega`, and conservation of axial angular momentum
  for negligible external torque. Friction is the internal coupling mechanism.
- **Answer separation:** the supplied answer C and printed `100 rpm` are
  represented as metadata. The theorem must still derive that the independent
  final observable equals that value.

## Declarations created and blueprint labels

The assigned Lean file contains the declarations pinned by the chapter:

| Lean declaration (namespace `PhyXMiniProblems.ProblemPhyXMini0712`) | Blueprint label |
|---|---|
| `momentOfInertiaDimension` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-momentofinertiadimension` |
| `angularMomentumDimension` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-angularmomentumdimension` |
| `LengthQuantity` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-lengthquantity` |
| `MassQuantity` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-massquantity` |
| `AxialAngularVelocity` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-axialangularvelocity` |
| `AxialMomentOfInertia` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-axialmomentofinertia` |
| `AxialAngularMomentum` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-axialangularmomentum` |
| `nonnegativeSIReadout` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-nonnegativesireadout` |
| `signedSIReadout` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-signedsireadout` |
| `lengthInMeters` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-lengthinmeters` |
| `massInKilograms` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-massinkilograms` |
| `angularVelocityInRadiansPerSecond` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-angularvelocityinradianspersecond` |
| `angularVelocityInRevolutionsPerMinute` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-angularvelocityinrevolutionsperminute` |
| `momentOfInertiaInKilogramMetersSquared` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-momentofinertiainkilogrammeterssquared` |
| `angularMomentumInKilogramMetersSquaredPerSecond` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-angularmomentuminkilogrammeterssquaredpersecond` |
| `RotatingBody` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-rotatingbody` |
| `RotatingBodyShape` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-rotatingbodyshape` |
| `FigureStage` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-figurestage` |
| `AxialDirection` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-axialdirection` |
| `DiskLoopFigureLabel` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-diskloopfigurelabel` |
| `DiskLoopFigure` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-diskloopfigure` |
| `DiskLoopRotationSetup` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-disklooprotationsetup` |
| `MatchesPrimaryDiskLoopFigure` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-matchesprimarydiskloopfigure` |
| `MatchesDiskLoopProblemData` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-matchesdiskloopproblemdata` |
| `HasPhysicalDiskLoopParameters` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-hasphysicaldiskloopparameters` |
| `SatisfiesDiskAndLoopMomentOfInertiaLaws` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-satisfiesdiskandloopmomentofinertialaws` |
| `SatisfiesIsolatedFrictionalAngularMomentumLaw` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-satisfiesisolatedfrictionalangularmomentumlaw` |
| `diskMomentOfInertia_equals_loopMomentOfInertia` | `lem:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-diskmomentofinertia-equals-loopmomentofinertia` |
| `finalCommonAngularVelocity_formula` | `lem:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-finalcommonangularvelocity-formula` |
| `AnswerChoice` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-answerchoice` |
| `AnswerChoice.revolutionsPerMinute` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-answerchoice-revolutionsperminute` |
| `recordedDatasetAnswer` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-recordeddatasetanswer` |
| `MatchesAnswerChoice` | `def:physics:phyx-mini-0712:phyxminiproblems-problemphyxmini0712-matchesanswerchoice` |
| `finalAngularVelocity_is_100_rpm` | `thm:physics:phyx_mini_0712:target` |

## LeanExplore queries/candidates actually used

Every iteration-003 search used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `angular momentum conservation rigid body rotation
  moment of inertia angular velocity` returned
  `RigidBody.angularMomentum_eq_inertiaTensor_mulVec`,
  `RigidBodyMotion.angularVelocity`, `RigidBody.angularMomentum`, and
  `RigidBody.inertiaTensor` among the leading candidates.
- Likely-name query `RigidBody.angularMomentum inertiaTensor angularVelocity`
  confirmed those same Physlib rigid-body declarations.
- Natural-language query `moment of inertia solid disk thin circular loop`
  found generic `RigidBody.inertiaTensor` and the solid-sphere declarations
  `RigidBody.solidSphere`/`RigidBody.solidSphere_inertiaTensor`, but no solid
  disk or thin circular loop constructor/formula.
- Natural-language query `physical dimension mass length time SI units`
  found `UnitChoices.SI`, `Dimension`, `Dimension.L𝓭`, and `Dimension.T𝓭`.
- Likely-name queries `Dimensionful WithDim UnitChoices.SI`, `WithDim`,
  `Dimension.M𝓭`, and `Real.pi` grounded the exact representation and
  conversion names used in the file.

Source and module data were fetched in iteration 003 only for candidates used
by this formalization:

- `WithDim` from `Physlib.Units.WithDim.Basic`;
- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`;
- `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, and `Dimension.M𝓭` from
  `Physlib.Units.Dimension`;
- `Real.pi` from
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`,
  `Dimension.M𝓭`, `Dimension.T𝓭`, and `UnitChoices.SI`.
- Mathlib: `Real.pi`, `NNReal`, real arithmetic and powers, and the finite and
  decidable instances used by the inductive figure/answer vocabularies.
- The fetched sources confirm that `Dimensionful` is the unit-dependent
  representation satisfying the dimensional scaling law, `WithDim` carries a
  dimension tag and underlying value, and `UnitChoices.SI` selects metres,
  seconds, and kilograms (along with the other SI base units).

## Local abstractions introduced

- `AxialAngularVelocity`, `AxialMomentOfInertia`, and
  `AxialAngularMomentum` specialize Physlib's dimension-tagged quantities to
  the scalar components about the drawn symmetry axis. Signed carriers retain
  orientation; lengths, masses, and inertia magnitudes use nonnegative
  carriers.
- `momentOfInertiaDimension` and `angularMomentumDimension` construct the
  missing composite dimensions from Physlib's base dimensions.
- `DiskLoopFigure`, its enums, and `MatchesPrimaryDiskLoopFigure` preserve the
  qualitative geometry and visible labels without turning drawing coordinates
  into physical measurements.
- `DiskLoopRotationSetup` keeps the physical observables independent.
- `SatisfiesDiskAndLoopMomentOfInertiaLaws` is the smallest local shape-law
  interface because the search found no ready-made solid-disk/thin-loop
  specializations.
- `SatisfiesIsolatedFrictionalAngularMomentumLaw` is the smallest scalar axial
  interface for before/after `L = I omega` and conservation. It contains no
  requested final value.
- `AnswerChoice` and `MatchesAnswerChoice` preserve the distinction between
  displayed answer metadata and the physical result.

## Grounding gaps and redraft requests

- Physlib's available rigid-body angular momentum and inertia declarations are
  vector/tensor continuum machinery; LeanExplore found no ready-made solid disk
  or thin-loop inertia theorem. The local dimensionful axial interface is
  therefore retained.
- The auxiliary caption says the loop initially rotates, conflicting with the
  problem prose and primary image. The formalization follows the stronger
  evidence: the disk rotates initially and the dropped loop has zero initial
  axial spin. A source/blueprint editor may wish to correct that caption.
- The requested `.archon/AGENTS.md` is absent. The applicable role instructions
  were read from `.archon/prover-modes/physics-formalize.md` together with
  `.archon/PROGRESS.md`.
- The blueprint is marked `% archon:physics` and already has all `\lean{...}`
  pins, but its environments do not contain `\leanok`. This agent did not edit
  the blueprint because the explicit write permissions allow edits only to the
  assigned Lean file and this result file. A coordinator with blueprint write
  permission should add the appropriate `\leanok` markers.

## Verification

- `archon-lean-lsp` diagnostics succeeded with exactly three expected
  `declaration uses sorry` warnings, for the two derived lemmas and target
  theorem, and no errors or failed dependencies.
- The LSP outline confirmed the imports and the target theorem signature.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0712.lean` exited with code
  `0`; its only output was the same three expected `sorry` warnings.

