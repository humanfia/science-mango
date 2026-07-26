# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0786.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0786.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `speed Dimension`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `angular Speed Dimension`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `acceleration Dimension`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `force Dimension`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `moment Of Inertia Dimension`
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `ProbabilityTheory.moment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment of a real random variable, `μ[X ^ p]`.
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `Angular Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed.oneMilePerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 mile per hour.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimSpeed` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `DimSpeed` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `ProbabilityTheory.moment` (Mathlib)
- `Momentum` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed.oneMilePerHour` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0786.AccelerationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.AngularSpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.CircularTrackContactSide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.FigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.ForceMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.HasPhysicalRollingShellParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.IsMarginallyInContactAtA`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.LoopPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.MomentOfInertiaQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.MotionPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.RelativeScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.RollingFrictionWorkModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.RollingMode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.RollingShellLoopSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SatisfiesCircularTrackRadialDynamics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SatisfiesConservativeRollingEnergyLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SatisfiesRollingWithoutSlipLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SatisfiesThinHollowShellInertiaLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.ShellMassModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0786.SuppliedRollingShellFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
