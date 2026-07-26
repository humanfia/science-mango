# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0870.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0870.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:18b3d6d159578ebb9fee13b03e728bef2aab519192e8cad3aac7fc3281933eb8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `electric Potential Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.instZero` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The electromagnetic potential in $d$ dimensions admits a zero element, defined as the potential that assigns the value zero to every point in its domain.
- `Electromagnetism.DistElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Distributional.ElectricField` | package PhysLean | The electric field of an electromagnetic potential which is a distribution.

### Query: `electric Field Strength Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inl_inr_eq_electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Relationship Between the Electromagnetic Field Strength Matrix and the Electric Field.** For a differentiable electromagnetic potential $A$ in a $(d+1)$-dimensional spacetime with speed of light $c$, the components...
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Matrix.** For a given electromagnetic potential $A$ and speed of light $c$, the $i$-th component of the electric field $\mathbf{E}$ at time $t$ and position $x$ is...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Electric Potential Quantity`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.zero_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The value of the zero electromagnetic potential is equal to zero.
- `Electromagnetism.ElectromagneticPotential.electricField_eq` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field in Terms of Potentials.** For an electromagnetic potential $A$ in $d$ spatial dimensions and a given speed of light $c$, the associated electric field at time $t$ and position $x$ is equal to the nega...

### Query: `Electric Field Strength Quantity`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.DistElectromagneticPotential.electricField_eq_fieldStrength` | module `Physlib.Electromagnetism.Distributional.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Tensor.** For a distributional electromagnetic potential $A$ in $d$-dimensional spacetime and a speed of light $c$, the $i$-th component of the associated electric...
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Matrix.** For a given electromagnetic potential $A$ and speed of light $c$, the $i$-th component of the electric field $\mathbf{E}$ at time $t$ and position $x$ is...

### Query: `Planar Position Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Orthogonality of Basis Charges and Even-Indexed Planes.** For any two distinct indices $k$ and $j$ in $\{0, \dots, n\}$, the $k$-th basis charge evaluated on the first vector of the $j$-th even plane is zero.
- `PureU1.VectorLikeEvenPlane.P_evenFst` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Projection onto the First Basis Element of an Even Plane.** For any charge distribution $f$ indexed by $\{0, \dots, n\}$ and any index $j$, the linear functional $P$ evaluated at the $j$-th basis vector of the even...

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.instZero` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inl_inr_eq_electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.zero_val` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.electricField_eq_fieldStrength` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` (PhysLean)
- `PureU1.VectorLikeEvenPlane.P_evenFst` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0870.AdjacentGap`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.AnswerMatchesFieldStrength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.ElectricFieldStrengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.ElectricPotentialQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.EquipotentialLine`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.EquipotentialMapFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.EquipotentialMapSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.HasPhysicalEquipotentialSpacing`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.MatchesSuppliedEquipotentialFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.PlanarPositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0870.SatisfiesElectrostaticEquipotentialLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
