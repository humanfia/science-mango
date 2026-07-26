# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0418.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0418.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Volume Quantity`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `Pressure Quantity`
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimPressure.psi` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pound per square inch.

### Query: `Work Quantity`
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `volume In Cubic Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.

### Query: `volume In Cubic Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.

### Query: `pressure In Pascals`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `pressure In Kilopascals`
- `DimPressure.bar` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 bar (100,000 pascals).
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `work In Joules`
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `joules Per Kilopascal Cubic Centimeter`
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Cubic` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | The structure representing a cubic polynomial.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `DimPressure` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimPressure.psi` (PhysLean)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)
- `DimPressure.bar` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure` (PhysLean)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `JoinedIn` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Cubic` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0418.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.ArrowDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.AxisDisplayUnit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.AxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.AxisSymbol`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.CycleLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.CycleOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.CycleVertex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.FigureAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.HasPhysicalCycleParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.MatchesProblemAndPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.MaximumPressureMatchesChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.PathShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.PressureQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.PressureVolumeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.SatisfiesTriangularCycleBoundaryWorkLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.TriangularPVCycleSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.UsesGivenCycleWork`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.WorkQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0418.WorkingSubstance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
