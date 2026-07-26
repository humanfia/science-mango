# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0869.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0869.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:85a6826493c2bca9596182c2ab5e5a0fc4b3706828b6c935dfc33b7eedcf9bad
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `electric Potential Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.instZero` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The electromagnetic potential in $d$ dimensions admits a zero element, defined as the potential that assigns the value zero to every point in its domain.
- `Electromagnetism.DistElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Distributional.ElectricField` | package PhysLean | The electric field of an electromagnetic potential which is a distribution.

### Query: `electric Field Component Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `Electric Potential Quantity`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.zero_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The value of the zero electromagnetic potential is equal to zero.
- `Electromagnetism.ElectromagneticPotential.electricField_eq` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field in Terms of Potentials.** For an electromagnetic potential $A$ in $d$ spatial dimensions and a given speed of light $c$, the associated electric field at time $t$ and position $x$ is equal to the nega...

### Query: `Signed Electric Field Component Quantity`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.DistElectromagneticPotential.electricField_eq_fieldStrength` | module `Physlib.Electromagnetism.Distributional.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Tensor.** For a distributional electromagnetic potential $A$ in $d$-dimensional spacetime and a speed of light $c$, the $i$-th component of the associated electric...

### Query: `electric Potential In Volts`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.zero_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The value of the zero electromagnetic potential is equal to zero.
- `Electromagnetism.ElectromagneticPotential.electricField_eq` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field in Terms of Potentials.** For an electromagnetic potential $A$ in $d$ spatial dimensions and a given speed of light $c$, the associated electric field at time $t$ and position $x$ is equal to the nega...

### Query: `electric Field Component In Volts Per Meter`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Matrix.** For a given electromagnetic potential $A$ and speed of light $c$, the $i$-th component of the electric field $\mathbf{E}$ at time $t$ and position $x$ is...
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Plot Axis`
- `Diffeology.isPlot_const` | module `Mathlib.Geometry.Diffeology.Basic` | package Mathlib | **Constant Maps are Plots.** For any diffeological space $X$ and any point $x \in X$, the constant map from the Euclidean space $\mathbb{R}^n$ to $X$ defined by $v \mapsto x$ is a plot of $X$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Plot Axis Role`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Diffeology.isPlot_id` | module `Mathlib.Geometry.Diffeology.Basic` | package Mathlib | **Identity Map as a Plot.** The identity map on the Euclidean space $\mathbb{E}^n$ is a plot of its natural diffeology.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.instZero` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.zero_val` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.electricField_eq_fieldStrength` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.zero_val` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `Diffeology.isPlot_const` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Diffeology.isPlot_id` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0869.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.CalibratesPhyslibElectricField`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.ElectricFieldGraphFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.ElectricPotentialQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.ElectrostaticLineSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.MatchesElectrostaticScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.MatchesPrimaryElectricFieldGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.PlotAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.PlotAxisRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.SatisfiesElectrostaticPotentialDifferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.SignedElectricFieldComponentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.TraceColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0869.UsesStatedOriginPotential`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
