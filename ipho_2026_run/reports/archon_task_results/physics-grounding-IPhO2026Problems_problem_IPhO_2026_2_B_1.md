# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:921cf8299fdd98e7ac0a482b26e58fed7a68a2c2e5af60158fc4d5dbf81d0710
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `PhysicalLength`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `Dimension.L𝓭_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Component.** The length component of the fundamental physical dimension for length is equal to 1.

### Query: `radiantPowerDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `solarIntensityDimension`
- `MassUnit.nominalSolarMasses` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The mass unit of nominal solar masses (1.988416 × 10 ^ 30 kilograms). See: https://iopscience.iop.org/article/10.3847/0004-6256/152/2/41
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `RadiantPower`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `QuantumMechanics.radiusPowOperator_hasDenseDomain` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | **Dense Domain of the Radial Power Operator.** For any real number $s$, the radial power operator $\mathcal{R}^s$ has a dense domain.

### Query: `SolarIntensity`
- `MassUnit.nominalSolarMasses` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The mass unit of nominal solar masses (1.988416 × 10 ^ 30 kilograms). See: https://iopscience.iop.org/article/10.3847/0004-6256/152/2/41
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `IntervalIntegrable.intervalIntegrable_slope` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope` | package Mathlib | If `f` is interval integrable on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.

### Query: `scaleLength`
- `LengthUnit.scale` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The scaling of a length unit by a positive real.
- `LengthUnit.scale_scale` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Composition of Scaling for Length Units.** For any length unit $x$ and any two positive real numbers $r_1$ and $r_2$, scaling $x$ by $r_2$ and then scaling the result by $r_1$ is equivalent to scaling $x$ by the pro...
- `LengthUnit.scale_one` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Identity of Scaling for Length Units.** Scaling any length unit by a factor of 1 results in the original length unit.

### Query: `CrossSection`
- `crossProduct` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | The cross product of two vectors in $R^3$ for $R$ a commutative ring.
- `Mathlib.CrossRef.Tag` | module `Mathlib.Tactic.CrossRefAttribute` | package Mathlib | A cross-reference from a Mathlib declaration to an entry in an external database.
- `cross_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Vector Triple Product Identity.** For any three vectors $u, v, w \in R^3$ over a commutative ring $R$, the iterated cross product satisfies the identity $u \times (v \times w) = u \times (v \times w) - v \times (u \...

### Query: `AxisDirection`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `RayDirection2D`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | **Same Ray Condition in Two Dimensions.** For any two vectors $x$ and $y$ in an oriented two-dimensional inner product space, $x$ and $y$ lie on the same ray if and only if their inner product is non-negative and the...
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `ParallelDirections`
- `CategoryTheory.Limits.parallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with common domain and codomain.
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result
- `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` | package Mathlib | **Equivalence of Parallelism and Directional Equality.** Two affine subspaces $s_1$ and $s_2$ are parallel if and only if they have the same direction and $s_1$ is empty if and only if $s_2$ is empty.

## Grounded Mathlib/PhysLean names

- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Dimension` (PhysLean)
- `Dimension.L𝓭_length` (PhysLean)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `MassUnit.nominalSolarMasses` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `QuantumMechanics.radiusPowOperator_hasDenseDomain` (PhysLean)
- `MassUnit.nominalSolarMasses` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `IntervalIntegrable.intervalIntegrable_slope` (Mathlib)
- `LengthUnit.scale` (PhysLean)
- `LengthUnit.scale_scale` (PhysLean)
- `LengthUnit.scale_one` (PhysLean)
- `crossProduct` (Mathlib)
- `Mathlib.CrossRef.Tag` (Mathlib)
- `cross_cross` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `SameRay` (Mathlib)
- `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `CategoryTheory.Limits.parallelPair` (Mathlib)
- `Computation.parallel` (Mathlib)
- `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_B_1.AxisDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.CrossSection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.Figure2fReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.IsAdmissibleIncidenceAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.IsRadiusCoefficientFormula`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.LightRay2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.OpticalPath2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.ParallelDirections`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.PhysicalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.PointLiesOnForwardRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.RadiantPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.RayDirection2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.SolarCookerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.SolarIntensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.ValidSolarCookerPhysics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
