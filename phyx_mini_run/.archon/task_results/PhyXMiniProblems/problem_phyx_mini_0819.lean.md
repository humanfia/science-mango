## Assumption/target split

### Governing laws

- `SatisfiesThreeDiskRotationalLaws.pointMassMomentOfInertiaAboutAxis1` states the general point-mass axial-inertia sum `I = Σ m r²` for disks A, B, and C after applying the stated small-disk and lightweight-strut idealization.
- `rigidBodyMassIsDiskMassSum` and `axis1TensorEntryMatchesScalarInertia` connect the labeled physical model to Physlib's `RigidBody.mass` and `RigidBody.inertiaTensor` SI-coordinate interface.
- `angularVelocityIsAlongAxis1` states that the angular-velocity vector has only the axis-1 component.
- `rotationalEnergyUsesPhyslib` connects the independent dimensionful energy observable to `RigidBody.rotationalKineticEnergy` for every angular speed. It contains neither the given speed nor either answer value.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- Figure labels: disks A/B/C; struts AB/BC/CA; axes 1 and 2.
- Printed masses: `m_A = 0.30 kg`, `m_B = 0.10 kg`, `m_C = 0.20 kg`.
- Printed center-to-center strut lengths: `AB = 0.50 m`, `BC = 0.30 m`, `CA = 0.40 m`.
- Axis geometry: axis 1 passes through A perpendicular to the triangular frame; axis 2 lies along and passes through B and C.
- Figure-derived axis-1 radii: `r_A = 0`, `r_B = AB`, and `r_C = CA`. The axis-2 zero radii of B and C are also recorded even though they do not enter the requested calculation.
- Problem data: selected axis 1, angular speed `4 rad/s`, point-mass-at-center model for the small disks, and negligible-mass model for the lightweight struts.

### Current target conclusions

- `axis1MomentOfInertia_eq_57_over_1000`: `I₁ = 0.057 kg m²`.
- `rotationalKineticEnergy_eq_half_inertia_mul_angularSpeed_sq`: reduction of Physlib's tensor contraction to `K = Iω²/2` for axis-aligned angular velocity.
- `axis1KineticEnergyAtFour_eq_57_over_125`: exact model energy `K = 0.456 J`.
- `kineticEnergyAboutAxis1_is_answer_B`: the exact energy lies in the nearest-hundredth bin for `0.46 J`, and B is the unique closest displayed choice.

## Goal-faithfulness audit

The exact `57/125 J` result, the rounded `23/50 J` value, and the correctness/uniqueness of answer B appear only in lemma or theorem conclusions. `ThreeDiskMachinePart.rotationalKineticEnergy` is an independent physical observable, not a definition built from an option. `SatisfiesThreeDiskRotationalLaws` contains only general inertia/tensor/energy laws; it does not mention `4 rad/s`, `0.456 J`, `0.46 J`, or an answer label. `MatchesProblemData` supplies the requested speed and physical idealizations but no energy result. `recordedAnswerChoice := .B` is explicitly source metadata, while the theorem must independently establish that this recorded choice is uniquely closest.

The rounding distinction is intentional: the supplied exact decimal data give
`(1/2) * (0.10 * 0.50² + 0.20 * 0.40²) * 4² = 0.456 J`, not the exact equality `0.46 J`. The final statement therefore models `0.46 J` as the displayed nearest-hundredth answer rather than asserting a false exact equality.

## Declarations created and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0819:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0819.kineticEnergyAboutAxis1_is_answer_B`.
- Supporting physical conclusions are `axis1MomentOfInertia_eq_57_over_1000`, `rotationalKineticEnergy_eq_half_inertia_mul_angularSpeed_sq`, and `axis1KineticEnergyAtFour_eq_57_over_125`.
- Dimensionful roles are represented by `MassQuantity`, `LengthQuantity`, `AngularSpeedQuantity`, `MomentOfInertiaQuantity`, and `EnergyQuantity`.
- Figure vocabulary and setup are represented by `DiskLabel`, `StrutLabel`, `AxisLabel`, `AxisOrientation`, `ThreeDiskFigure`, and `ThreeDiskMachinePart`.
- Assumption interfaces are `MatchesPrimaryFigure`, `MatchesProblemData`, and `SatisfiesThreeDiskRotationalLaws`.
- Multiple-choice metadata/relations are `EnergyAnswerChoice`, `displayedEnergyJoules`, `recordedAnswerChoice`, `RoundsToNearestHundredth`, `IsClosestEnergyChoice`, and `IsUniqueClosestEnergyChoice`.

The chapter already existed and contained `% archon:physics`. It was not edited because the task's explicit write permissions allow changes only to the assigned Lean file and this result file. The orchestrator/plan owner should add `\leanok` to the blueprint theorem environment after accepting this formalization.

## LeanExplore queries and candidates actually used

- Natural-language query: `rotational kinetic energy equals one half moment of inertia times angular velocity squared`.
  - Used candidate `RigidBody.rotationalKineticEnergy` (declaration id 385448), module `Physlib.ClassicalMechanics.RigidBody.KineticEnergy`.
- Natural-language query: `moment of inertia point masses sum mass times radius squared`.
  - No direct discrete point-mass sum declaration was returned. The nearby `RigidBody.inertiaTensor` infrastructure was used together with a faithful local point-mass law.
- Likely-name query: `rotationalKineticEnergy momentOfInertia angularVelocity`.
  - Confirmed `RigidBody.rotationalKineticEnergy`; `RigidBodyMotion.angularVelocity` was inspected but not used because it represents a time-dependent full rigid-body motion, whereas this problem supplies a fixed scalar angular speed about a named axis.
- Likely-name query: `RigidBody.inertiaTensor`.
  - Used `RigidBody.inertiaTensor` (id 385416), module `Physlib.ClassicalMechanics.RigidBody.Basic`, and `RigidBody` (id 385412).
- Natural-language queries: `SI units mass length energy joule kilogram meter`, `dimensionful physical quantity with units and SI value`, `Quantity Dimension Mass Length Time Physlib units`, and `DimEnergy joule SI value`.
  - Used `UnitChoices.SI` (id 394270), `Dimensionful` (id 394284), `WithDim` (id 394425), `Dimension`/`L𝓭`/`T𝓭`, `DimEnergy` (id 394468), and `DimEnergy.joule` (id 394469).
- Queries for `DimMass`, `DimLength`, and dimensional angular velocity found no matching convenience types suitable for these nonnegative scalar magnitudes. The file therefore instantiates Physlib's generic `Dimensionful (WithDim d NNReal)` interface at the required dimensions.

All LeanExplore calls used package filters `Mathlib` and `Physlib`.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `M𝓭`, `L𝓭`, `T𝓭`.
- `UnitChoices.SI`.
- `DimEnergy` and `DimEnergy.joule`.
- `RigidBody`, `RigidBody.mass`, `RigidBody.inertiaTensor`, and `RigidBody.rotationalKineticEnergy`.
- Mathlib's `NNReal`, `Fin`, real arithmetic, finite inductive types, and absolute-value notation are used through the imported Physlib/Mathlib modules.

## Local abstractions introduced

- Dimension aliases instantiate Physlib's dimension-tagged quantities for mass, length, inverse-time angular speed, and mass-length-squared inertia. They are not aliases to bare scalars: each is a unit-independent `Dimensionful` quantity with an explicit physical dimension.
- `ThreeDiskFigure` preserves literal labels, endpoints, printed readouts, and axis incidence/orientation from the primary image.
- `SmallDiskModel.pointMassAtCenter` and `StrutMassModel.negligible` state the minimum idealizations needed because no disk radii or strut masses are supplied.
- `SatisfiesThreeDiskRotationalLaws.pointMassMomentOfInertiaAboutAxis1` is local because LeanExplore returned no discrete point-mass inertia-sum theorem. It preserves the standard physical law and is connected to Physlib's tensor/energy definitions rather than replacing the requested answer with an assumption.
- `RoundsToNearestHundredth` separates the exact computed energy from the precision of the displayed answer choices.

## Grounding gaps

- Physlib provides a general mass-distribution `RigidBody`, its inertia tensor, and rotational kinetic energy, but LeanExplore exposed no ready-made theorem specializing axial inertia to a finite set of point masses. The local governing-law field supplies precisely that missing specialization.
- Physlib has no convenience alias found for nonnegative dimensionful angular speed or scalar moment of inertia, so generic `Dimensionful (WithDim ... NNReal)` instances are used.
- The advertised `archon dag-query` executable was not available on `PATH`, so no dependency-graph result could be recorded. The blueprint contains only the target environment and the source report lists no previous parts.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0819.lean` exits successfully. The only diagnostics are the four expected `declaration uses sorry` warnings for the three supporting lemmas and final theorem.
