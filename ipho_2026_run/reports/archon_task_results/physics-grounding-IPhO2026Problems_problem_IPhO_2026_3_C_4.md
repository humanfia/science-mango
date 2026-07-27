# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_C_4.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_4.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:5b439d31cc091e627f225c12c10f589503da436788402a680fa69e41f45e7bbc
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `energyDimension`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `volumeDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `BoxIntegral.Box.volume_face_mul` | module `Mathlib.Analysis.BoxIntegral.Partition.Measure` | package Mathlib | **Volume of a Box as a Product of Face Volume and Side Length.** For a rectangular box $I$ in $\mathbb{R}^{n+1}$ and any index $i \in \{0, \dots, n\}$, the volume of $I$ (defined as the product of its side lengths $\p...

### Query: `magneticIntensityDimension`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `heatCapacityDimension`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).

### Query: `powerDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `molarCurieConstantDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `Constants.kBAx` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`. As long as one does not use the underlying value of this quantity, then it can be used as Boltzmann's constant in an arbitrary set of units.

### Query: `EnergyReadout`
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `VolumeReadout`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `MeasureTheory.tacticVolume_tac` | module `Mathlib.MeasureTheory.Measure.MeasureSpaceDef` | package Mathlib | The tactic `exact volume`, to be used in optional (`autoParam`) arguments.

### Query: `MagneticIntensityReadout`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ElectromagneticPotential.magneticField` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The magnetic field from the electromagnetic potential.

### Query: `HeatCapacityReadout`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).
- `CanonicalEnsemble.fluctuation_dissipation_energy_parametric` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Parametric FDT: C_V = Var(E)/(kB T²), assuming Var(E) = - dU/dβ.

## Grounded Mathlib/PhysLean names

- `DimEnergy` (PhysLean)
- `dimH` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `BoxIntegral.Box.volume_face_mul` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `dimH` (Mathlib)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `Dimension` (PhysLean)
- `LocallyConstant` (Mathlib)
- `Constants.kBAx` (PhysLean)
- `Finpartition.energy` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `DimEnergy` (PhysLean)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `MeasureTheory.tacticVolume_tac` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `CanonicalEnsemble.fluctuation_dissipation_energy_parametric` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_C_4.AmountOfSubstanceReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.ContinuousCoolingRun`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.CyclePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.EnergyReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.FollowsFigureThreeB`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.HasPhysicalOperatingRange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.HeatCapacityReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.IPhO_2026_3_C_4_elapsedTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.MagneticIntensityReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.ObeysContinuousCarnotCoolingLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.ObeysParamagneticEquationOfState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.ParamagneticCarnotCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.PowerReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.TimeReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.VolumeReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
