# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0797.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0797.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2537b9c66330487a5290494ea0fcde8b965164eeaed0a384ef77308e5181fd0a
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

### Query: `velocity Dimension`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `FluidDynamics.VelocityField` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A velocity field on `d`-dimensional space.

### Query: `Planar Velocity Quantity`
- `RigidBodyMotion.velocityClosedForm_val` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The closed-form velocity as a plain vector-valued function of the coordinates of `y`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.

### Query: `kilometer Hour Units`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.

### Query: `velocity Readout`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | The trajectory resulting from `toInitialConditions` has the specified velocity `v_t₀` at time `t₀`.

### Query: `velocity In Kilometers Per Hour`
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `DimSpeed.oneMilePerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one mile per hour to SI units.** The value of one mile per hour, when expressed in the International System of Units (SI), is exactly $0.44704$ meters per second.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.

### Query: `speed In Kilometers Per Hour`
- `DimSpeed.oneMilePerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one mile per hour to SI units.** The value of one mile per hour, when expressed in the International System of Units (SI), is exactly $0.44704$ meters per second.
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.

### Query: `east Hat`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `Mathlib.Tactic.Erw?.extractRewriteHypEq` | module `Mathlib.Tactic.ErwQuestion` | package Mathlib | Checks that the input `Expr` represents a proof produced by `(e)rw at` and returns the type of the LHS of the equality (from the lemma used). This will be defeq to the hypothesis being written, but not necessarily red...

### Query: `north Hat`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Affine.Simplex.direction_altitude` | module `Mathlib.Geometry.Euclidean.Altitude` | package Mathlib | The direction of an altitude.
- `stereoInvFun_ne_north_pole` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Inverse Stereographic Projection Avoids the North Pole.** For any unit vector $v$ in a real inner product space $E$, the inverse stereographic projection from the orthogonal complement of the span of $v$ into the un...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `FluidDynamics.VelocityField` (PhysLean)
- `RigidBodyMotion.velocityClosedForm_val` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `Units` (Mathlib)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` (PhysLean)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `DimSpeed.oneMilePerHour_in_SI` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `DimSpeed.oneMilePerHour_in_SI` (PhysLean)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Tactic.Erw?.extractRewriteHypEq` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Affine.Simplex.direction_altitude` (Mathlib)
- `stereoInvFun_ne_north_pole` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0797.AirplaneVelocityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.AirplaneWindSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.CardinalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.DiagramDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.DiagramPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.MatchesDisplayedGroundSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.MatchesStatedDirections`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.ObeysDirectionalMeasurementModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.ObeysGalileanVelocityComposition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.PhysicalSystem`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.PlanarVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.RelativeVelocityLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0797.RepresentsFigureDriftAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
