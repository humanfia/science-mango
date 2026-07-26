# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0722.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0722.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e38964caaaa905323d292cd854b7566902aa8c29b6f4d62aba35898d387b9261
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `volume Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `BoxIntegral.Box.volume_face_mul` | module `Mathlib.Analysis.BoxIntegral.Partition.Measure` | package Mathlib | **Volume of a Box as a Product of Face Volume and Side Length.** For a rectangular box $I$ in $\mathbb{R}^{n+1}$ and any index $i \in \{0, \dots, n\}$, the volume of $I$ (defined as the product of its side lengths $\p...

### Query: `mass Density Dimension`
- `Dimension.one_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass Dimension of Unity.** The mass dimension of the identity dimension $1$ is equal to $0$.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `Dimension.inv_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass Dimension of an Inverse.** The mass dimension of the inverse of a physical dimension is equal to the negation of the mass dimension of the original dimension.

### Query: `acceleration Dimension`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `force Dimension`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Volume Quantity`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `Mass Density Quantity`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Acceleration Quantity`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Acceleration of a Harmonic Oscillator Trajectory.** For a harmonic oscillator with angular frequency $\omega$ and initial conditions $x_0$ and $v_0$, the second time derivative of the position trajectory $x(t)$ is g...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `BoxIntegral.Box.volume_face_mul` (Mathlib)
- `Dimension.one_mass` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `Dimension.inv_mass` (PhysLean)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `FluidDynamics.MassDensity` (PhysLean)
- `MassUnit` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_acceleration` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0722.AccelerationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.BlockMaterial`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.FigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.FluidKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.ForceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.HasPhysicalSubmergedBlockParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.ImmersionState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.IsNearestDisplayedTension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MassDensityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MatchesSubmergedBlockProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MatchesSubmergedWoodBlockScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MatchesSuppliedSubmergedBlockFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.MotionState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.RoundsToNearestTenthNewton`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.SatisfiesCubeAndDisplacementLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.SatisfiesSubmergedBlockStaticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.StringAttachment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.SubmergedWoodBlockSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.SuppliedSubmergedBlockFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.UsesStandardWaterAndGravity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0722.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
