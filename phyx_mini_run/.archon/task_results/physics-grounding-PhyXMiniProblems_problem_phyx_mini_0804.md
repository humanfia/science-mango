# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0804.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0804.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b5bad364b618a26b92ad6e22a320358612ba15a243e8ad74fff72bbdce856cd3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `acceleration Dimension`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `force Dimension`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Acceleration Component Quantity`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Acceleration of a Harmonic Oscillator Trajectory.** For a harmonic oscillator with angular frequency $\omega$ and initial conditions $x_0$ and $v_0$, the second time derivative of the position trajectory $x(t)$ is g...

### Query: `Force Component Quantity`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `PureU1.VectorLikeEvenPlane.Pa_zero!` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Vanishing of the Charge Component.** Given a vector $f \in \mathbb{Q}^{n+1}$ and a vector $g \in \mathbb{Q}^n$, if the charge assignment $Pa(f, g)$ is equal to zero, then every component of the vector $g$ must be zero.
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.

### Query: `mass Readout`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `acceleration Component Readout`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Acceleration of a Harmonic Oscillator Trajectory.** For a harmonic oscillator with angular frequency $\omega$ and initial conditions $x_0$ and $v_0$, the second time derivative of the position trajectory $x(t)$ is g...

### Query: `force Component Readout`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `Stream'.Seq.forceToList` | module `Mathlib.Data.Seq.Defs` | package Mathlib | Translate a sequence to a list. This function will run forever if run on an infinite sequence.

### Query: `mass In Kilograms`
- `MassUnit.kilograms` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The definition of a mass unit of kilograms.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `connectedComponent` (Mathlib)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` (PhysLean)
- `connectedComponent` (Mathlib)
- `PureU1.VectorLikeEvenPlane.Pa_zero!` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `connectedComponent` (Mathlib)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` (PhysLean)
- `connectedComponent` (Mathlib)
- `FluidDynamics.BodyForce` (PhysLean)
- `Stream'.Seq.forceToList` (Mathlib)
- `MassUnit.kilograms` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `UnitChoices.SI_mass` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0804.AccelerationComponentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.BodyLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.CafeteriaPushSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.FigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.FigureOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.FigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.ForceComponentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.MatchesFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.SatisfiesFrictionlessNewtonianDynamics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0804.TraySide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
