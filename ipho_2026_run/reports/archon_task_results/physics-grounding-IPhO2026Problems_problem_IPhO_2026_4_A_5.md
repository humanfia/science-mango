# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_A_5.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_A_5.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:942c215632f328b5bba3a66c7ab72402236d78aef061e3aeab50b8907a4ea385
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Length`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.

### Query: `Volume`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `MassDensity`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `ThermalPressureCoefficient`
- `NVEHamiltonian.pressure` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.ThermoQuantities` | package PhysLean | Pressure, as a function of T. Defined as the conjugate variable to volume.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `siValue`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `DimArea.are_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of an Are in SI Units.** In the SI unit system, the value of one are is exactly 100.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

### Query: `ApparatusLabel`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Quiver.Labelling` | module `Mathlib.Combinatorics.Quiver.Subquiver` | package Mathlib | An `L`-labelling of a quiver assigns to every arrow an element of `L`.

### Query: `CylinderDimensions`
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HomologicalComplex.precylinder` | module `Mathlib.Algebra.Homology.Precylinder` | package Mathlib | The precylinder object of a homological complex that is given by `HomologicalComplex.cylinder`.

### Query: `Figure17Geometry`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` | module `Mathlib.Geometry.Euclidean.Angle.Sphere` | package Mathlib | **Thales' theorem**: For three distinct points, the angle at the second point is a right angle if and only if the second point lies on the sphere having the first and third points as diameter endpoints.

### Query: `AirColumnState`
- `Matrix.det_succ_column` | module `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` | package Mathlib | Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`.
- `Matrix.det_mul_column` | module `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` | package Mathlib | Multiplying each column by a fixed `v j` multiplies the determinant by the product of the `v`s.
- `Matrix.det_succ_column_zero` | module `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` | package Mathlib | Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0.

### Query: `pressurePascal`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

## Grounded Mathlib/PhysLean names

- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `FluidDynamics.MassDensity` (PhysLean)
- `MassUnit` (PhysLean)
- `NVEHamiltonian.pressure` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimPressure` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `DimArea.are_in_SI` (PhysLean)
- `UnitChoices.SI_charge` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Quiver.Labelling` (Mathlib)
- `UnitExamples.OddDimensions` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HomologicalComplex.precylinder` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` (Mathlib)
- `Matrix.det_succ_column` (Mathlib)
- `Matrix.det_mul_column` (Mathlib)
- `Matrix.det_succ_column_zero` (Mathlib)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_A_5.AirColumnState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.ApparatusLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.CylinderDimensions`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.ExperimentalConditions`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.Figure17Geometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.GoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.IsochoricAirExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.Length`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.MassDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.MatchesCoefficientDefinition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.MatchesOfficialExperimentalResult`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.PhysicalAdmissibility`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.PreviousPartA3Linearity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.SatisfiesIdealGasLawAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.SourceReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.ThermalPressureCoefficient`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_5.WithinUncertainty`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
