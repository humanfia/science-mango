# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0823.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0823.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a2e93f14648ce17a711b6a419079de6c75ef7a3136f65cac0d608f6b5bcffee3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Spatial Vector`
- `Lorentz.Vector.spatialPart` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Basic` | package PhysLean | Extract spatial components from a Lorentz vector, returning them as a vector in Euclidean space.
- `SpaceTime.space_toCoord_symm` | module `Physlib.SpaceAndTime.SpaceTime.Basic` | package PhysLean | **Spatial Component of a Spacetime Vector.** For a spacetime vector represented as a function $f: \{0\} \oplus \{0, \dots, d-1\} \to \mathbb{R}$, its spatial part is the vector in $\mathbb{R}^d$ whose $i$-th coordinat...
- `Lorentz.Vector.spatialCLM` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Basic` | package PhysLean | The spatial part of a Lorentz vector as a continuous linear map.

### Query: `force Dimension`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `torque Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `DimPressure.torr` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure).

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Position Vector Quantity`
- `QuantumMechanics.OneDimension.positionStates_generalized_eigenvector_positionOperatorUnbounded` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | **Generalized Eigenvectors of the Position Operator.** For any real number $x$, the position state $\delta_x$ is a generalized eigenvector of the unbounded position operator with eigenvalue $x$.
- `QuantumMechanics.positionCLM_apply` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | **Pointwise Evaluation of the Position Operator.** For any Schwartz function $\psi$ on $\mathbb{R}^d$ and any point $x \in \mathbb{R}^d$, the $i$-th component of the position operator applied to $\psi$ and evaluated a...
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Force Vector Quantity`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `instCoeFunDimensionfulForallUnitChoices` | module `Physlib.Units.Basic` | package PhysLean | **Coercion of Dimensionful Quantities to Functions.** Any dimensionful quantity associated with a type $M$ that carries a dimension can be naturally treated as a function that maps a choice of units to an element of $M$.
- `ClassicalMechanics.HarmonicOscillator.force` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The force of the classical harmonic oscillator defined as `- dU(x)/dx` where `U(x)` is the potential energy.

### Query: `Torque Vector Quantity`
- `DimPressure.torr` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure).
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `CovariantDerivative.torsion_antisymm` | module `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion` | package Mathlib | **Antisymmetry of the Torsion Tensor.** For a covariant derivative on a manifold, the torsion tensor at any point $x$ is antisymmetric with respect to its two tangent vector arguments. That is, for any two tangent vec...

### Query: `nonnegative Readout`
- `Mathlib.Meta.Positivity.Strictness.nonnegative` | module `Mathlib.Tactic.Positivity.Core` | package Mathlib | **Non-negative Strictness.** In the context of the positivity tactic, if an expression $e$ in a partially ordered type is proven to be greater than or equal to zero ($0 \le e$), then its strictness is classified as no...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CompactlySupportedContinuousMap.nnrealPart_neg_eq_zero_of_nonneg` | module `Mathlib.Topology.ContinuousMap.CompactlySupported` | package Mathlib | **Nonnegative Part of a Negated Nonnegative Function.** For any compactly supported continuous real-valued function $f$, if $f$ is non-negative (i.e., $f(x) \geq 0$ for all $x$), then the nonnegative part of its negat...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Lorentz.Vector.spatialPart` (PhysLean)
- `SpaceTime.space_toCoord_symm` (PhysLean)
- `Lorentz.Vector.spatialCLM` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `DimPressure.torr` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `QuantumMechanics.OneDimension.positionStates_generalized_eigenvector_positionOperatorUnbounded` (PhysLean)
- `QuantumMechanics.positionCLM_apply` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `instCoeFunDimensionfulForallUnitChoices` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.force` (PhysLean)
- `DimPressure.torr` (PhysLean)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `CovariantDerivative.torsion_antisymm` (Mathlib)
- `Mathlib.Meta.Positivity.Strictness.nonnegative` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CompactlySupportedContinuousMap.nnrealPart_neg_eq_zero_of_nonneg` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0823.AgreesAtTenNewtonMeterPrecision`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.FigureComponent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.ForceVectorQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.HandleExtension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.MatchesDownwardForceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.MatchesHandleGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.PipeFittingTorqueSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.PositionVectorQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.SatisfiesTorqueLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.SpatialVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.SuppliedWrenchFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.TorqueSense`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.TorqueVectorQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0823.WrenchPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
