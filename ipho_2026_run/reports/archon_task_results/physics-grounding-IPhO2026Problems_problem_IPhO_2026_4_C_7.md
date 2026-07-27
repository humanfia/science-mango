# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_C_7.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_7.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9fb62381b0f0ea89010d9181f89b48cbb015a176e5aa3d58cf0bf02bedbd2672
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `powerDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `thermalResistanceDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.L𝓭_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Temperature Component.** The temperature component of the length dimension is equal to zero.

### Query: `thermalConductivityDimension`
- `Dimension.Θ𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to temperature.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `specificHeatCapacityDimension`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `UnitChoices.dimScale` | module `Physlib.Units.Basic` | package PhysLean | Given two choices of units `u1` and `u2` and a dimension `d`, the element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d` when changing from units `u1` to `u2`.
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.

### Query: `DimLength`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `DimMass`
- `UnitExamples.EnergyMassWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `E = m c^2` using `WithDim`.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.

### Query: `DimTemperature`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.npow_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Temperature of a Dimension Power.** For any dimension $d$ and natural number $n$, the temperature of the $n$-th power of $d$ is equal to $n$ times the temperature of $d$.

### Query: `DimPower`
- `PowerBasis.dim_pos` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | **Positivity of Power Basis Dimension.** If $S$ is a nontrivial algebra over a commutative ring $R$, then the dimension of any power basis of $S$ is strictly positive.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `DimThermalResistance`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.npow_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Temperature of a Dimension Power.** For any dimension $d$ and natural number $n$, the temperature of the $n$-th power of $d$ is equal to $n$ times the temperature of $d$.

### Query: `DimThermalConductivity`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.npow_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Temperature of a Dimension Power.** For any dimension $d$ and natural number $n$, the temperature of the $n$-th power of $d$ is equal to $n$ times the temperature of $d$.

## Grounded Mathlib/PhysLean names

- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.L𝓭_temperature` (PhysLean)
- `Dimension.Θ𝓭` (PhysLean)
- `dimH` (Mathlib)
- `Dimension` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `UnitChoices.dimScale` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `UnitExamples.EnergyMassWithDim'` (PhysLean)
- `dimH` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Temperature` (PhysLean)
- `dimH` (Mathlib)
- `Dimension.npow_temperature` (PhysLean)
- `PowerBasis.dim_pos` (Mathlib)
- `dimH` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.npow_temperature` (PhysLean)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.npow_temperature` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_C_7.ApparatusGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.CylindricalConductionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimInverseTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimMass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimSpecificHeatCapacity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimThermalConductivity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.DimThermalResistance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.Figure17AndProcedureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.PreviousPartC6Data`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.PreviousPartC6Result`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_7.ThermalConductionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
