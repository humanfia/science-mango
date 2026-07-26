# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0654.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0654.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:61c1ca2b04cd5b1dc9165fdb31e5bbe8dcbd5318cc32e28bcfd8201d9fb1baf8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `momentum Dimension`
- `QuantumMechanics.momentumCLM` | module `Physlib.QuantumMechanics.Operators.Momentum` | package PhysLean | Component `i` of the momentum operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`.
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `QuantumMechanics.OneDimension.momentumOperator` | module `Physlib.QuantumMechanics.Operators.OneDimension.Momentum` | package PhysLean | The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking `ψ` to `- i ℏ ψ'`.

### Query: `action Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `WithDim.instMulActionNNReal` | module `Physlib.Units.WithDim.Basic` | package PhysLean | **Scalar Action on Dimension-Tagged Types.** Given a physical dimension $d$ and a type $M$ equipped with a scalar action of the nonnegative real numbers $\mathbb{R}_{\ge 0}$, the type of elements of $M$ tagged with di...

### Query: `acceleration Dimension`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Momentum Magnitude`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.linearMomentum_eq` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | **Linear Momentum of a Rigid Body.** For a rigid body in $d$-dimensional space, the linear momentum at any time $t$ is equal to the product of the body's total mass and the velocity of its center of mass at that time.

### Query: `Signed Momentum Quantity`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `QuantumMechanics.OneDimension.momentumOperator_eq_smul` | module `Physlib.QuantumMechanics.Operators.OneDimension.Momentum` | package PhysLean | **Definition of the Momentum Operator.** For any complex-valued function $\psi: \mathbb{R} \to \mathbb{C}$, the momentum operator applied to $\psi$ is the function defined by the product of the negative imaginary unit...

### Query: `Action Quantity`
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `Action` | module `Mathlib.CategoryTheory.Action.Basic` | package Mathlib | An `Action V G` represents a bundled action of the monoid `G` on an object of some category `V`. As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`, while when `V = Type` this is a `G`-...
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `Acceleration Quantity`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Acceleration of a Harmonic Oscillator Trajectory.** For a harmonic oscillator with angular frequency $\omega$ and initial conditions $x_0$ and $v_0$, the second time derivative of the position trajectory $x(t)$ is g...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `QuantumMechanics.momentumCLM` (PhysLean)
- `Momentum` (PhysLean)
- `QuantumMechanics.OneDimension.momentumOperator` (PhysLean)
- `Dimension` (PhysLean)
- `MulAction` (Mathlib)
- `WithDim.instMulActionNNReal` (PhysLean)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `Momentum` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.linearMomentum_eq` (PhysLean)
- `signedDist` (Mathlib)
- `Momentum` (PhysLean)
- `QuantumMechanics.OneDimension.momentumOperator_eq_smul` (PhysLean)
- `MulAction` (Mathlib)
- `Action` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0654.AccelerationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.ActionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.DustHoleEscapeSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.FigureLengthUnit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.HasPhysicalDustHoleParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.HoleCrossSectionShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.IsUniqueNearestDisplayedDepth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MarkerLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MatchesDustSpeckScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MatchesSuppliedDustHoleFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.MomentumMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.ObjectKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.SatisfiesGoodChanceEscapeBoundary`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.SatisfiesKineticAndGravitationalEnergyLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.SatisfiesMinimumUncertaintyLocalizationEstimate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.SignedMomentumQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.SuppliedDustHoleFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0654.UsesStandardQuantumAndGravityData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
