# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_C_6.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_6.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9fc9380f94fd57492c40132d36067b57cba1991038943602325932d09f2e7760
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `energyDimension`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `powerDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `thermalResistanceDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.L𝓭_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Temperature Component.** The temperature component of the length dimension is equal to zero.

### Query: `specificHeatCapacityDimension`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `UnitChoices.dimScale` | module `Physlib.Units.Basic` | package PhysLean | Given two choices of units `u1` and `u2` and a dimension `d`, the element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d` when changing from units `u1` to `u2`.
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.

### Query: `thermalConductivityDimension`
- `Dimension.Θ𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to temperature.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `DimTemperature`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.npow_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Temperature of a Dimension Power.** For any dimension $d$ and natural number $n$, the temperature of the $n$-th power of $d$ is equal to $n$ times the temperature of $d$.

### Query: `DimTime`
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.T𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the time dimension.** The mass dimension component of the time dimension $T_d$ is equal to zero.
- `HasDim` | module `Physlib.Units.Basic` | package PhysLean | This typeclass indicates that there is a dimension `dim M : Dimension` associated with the type `M`.

### Query: `DimLength`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `DimMass`
- `UnitExamples.EnergyMassWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `E = m c^2` using `WithDim`.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.

### Query: `DimArea`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `Order.krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension is defined to...
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

## Grounded Mathlib/PhysLean names

- `DimEnergy` (PhysLean)
- `dimH` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.L𝓭_temperature` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `UnitChoices.dimScale` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `Dimension.Θ𝓭` (PhysLean)
- `dimH` (Mathlib)
- `Dimension` (PhysLean)
- `Temperature` (PhysLean)
- `dimH` (Mathlib)
- `Dimension.npow_temperature` (PhysLean)
- `dim` (PhysLean)
- `Dimension.T𝓭_mass` (PhysLean)
- `HasDim` (PhysLean)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `UnitExamples.EnergyMassWithDim'` (PhysLean)
- `dimH` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `DimArea` (PhysLean)
- `Order.krullDim` (Mathlib)
- `DimArea.are` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_C_6.C5GraphReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimArea`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimHeatEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimHeatFlowRate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimInverseTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimMass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimSpecificHeatCapacity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimTemperatureGradient`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimTemperatureRate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimThermalConductivity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimThermalResistance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.Figure17Geometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.GoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.ProcedureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.TemperatureObservation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.ThermalExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_C_6.ThermalResistanceEstimate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
