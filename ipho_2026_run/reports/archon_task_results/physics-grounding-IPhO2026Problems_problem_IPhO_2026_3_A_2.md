# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_A_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c725ed04b2b318ae93fac10aff0d80cb0d00773dc6a60d4931322db583d9c9ab
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `DimLengthMagnitude`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `DimVolumeMagnitude`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `InnerProductSpace.volume_ball_of_dim_even` | module `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` | package Mathlib | **Volume of an Even-Dimensional Ball.** In a real inner product space $E$ of even dimension $n = 2k$, the volume of an open ball of radius $r$ centered at any point $x \in E$ is given by $$ \text{vol}(B(x, r)) = r^{2k...
- `CKMMatrix.VAbsub_ne_zero_Vud_Vus_ne_zero` | module `Physlib.Particles.FlavorPhysics.CKMMatrix.Relations` | package PhysLean | **Non-vanishing of the sum of squares of $V_{ud}$ and $V_{us}$ magnitudes.** For any CKM matrix $V$, if the magnitude of the element $V_{ub}$ is not equal to 1, then the sum of the squares of the magnitudes of the ele...

### Query: `DimElectricCurrent`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.DistElectromagneticPotential.threeDimPointParticleCurrentDensity` | module `Physlib.Electromagnetism.PointParticle.ThreeDimension` | package PhysLean | The current density of a point particle stationary at a point `r₀` of 3d space.
- `Electromagnetism.LorentzCurrentDensity.currentDensity` | module `Physlib.Electromagnetism.Dynamics.CurrentDensity` | package PhysLean | The underlying (non-Lorentz) current density associated with a Lorentz current density.

### Query: `DimMagneticFieldStrength`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Magnetic Field Components as Field Strength Matrix Elements.** For an electromagnetic potential $A$ that is differentiable over $\mathbb{R}$, the $i$-th spatial component of the magnetic field $\mathbf{B}$ at time $...
- `Electromagnetism.DistElectromagneticPotential.fieldStrength` | module `Physlib.Electromagnetism.Distributional.FieldStrength` | package PhysLean | The field strength of an electromagnetic potential which is a distribution.

### Query: `DimMagnetization`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `WithDim.val_neg` | module `Physlib.Units.WithDim.Basic` | package PhysLean | **Negation in WithDim.** For any element $m$ of the type $M$ equipped with a dimension $d$, the underlying value of the negation of $m$ is equal to the negation of the underlying value of $m$.

### Query: `DimMagneticFluxDensity`
- `FluidDynamics.NavierStokes.momentumFlux` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The convective momentum flux `rho u ⊗ u`.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `FluidDynamics.MomentumDensityField` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A momentum density field on `d`-dimensional space.

### Query: `DimMagneticFluxDensityIncrement`
- `Physlib.MultiIndex.increment` | module `Physlib.SpaceAndTime.Space.Derivatives.MultiIndex` | package PhysLean | Increment the `i`-th coordinate of a multi-index by one.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `SzemerediRegularity.increment` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Increment` | package Mathlib | The **increment partition** in Szemerédi's Regularity Lemma. If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition with a slightly higher energy. This is helpful since the...

### Query: `DimVacuumPermeability`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Electromagnetism.FreeSpace.ε₀_ne_zero` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | **Non-zero Vacuum Permittivity.** In any free space, the vacuum permittivity $\varepsilon_0$ is non-zero.

### Query: `DimVoltageImpulse`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.inv_charge` | module `Physlib.Units.Dimension` | package PhysLean | **Inverse Dimension Charge.** The electric charge component of the inverse of a physical dimension is equal to the negation of the electric charge component of the original dimension.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `InnerProductSpace.volume_ball_of_dim_even` (Mathlib)
- `CKMMatrix.VAbsub_ne_zero_Vud_Vus_ne_zero` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.threeDimPointParticleCurrentDensity` (PhysLean)
- `Electromagnetism.LorentzCurrentDensity.currentDensity` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.fieldStrength` (PhysLean)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `WithDim.val_neg` (PhysLean)
- `FluidDynamics.NavierStokes.momentumFlux` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `FluidDynamics.MomentumDensityField` (PhysLean)
- `Physlib.MultiIndex.increment` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `SzemerediRegularity.increment` (Mathlib)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Electromagnetism.FreeSpace.ε₀_ne_zero` (PhysLean)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.inv_charge` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_A_2.DimElectricCurrent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimLengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimMagneticFieldStrength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimMagneticFluxDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimMagneticFluxDensityIncrement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimMagnetization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimVacuumPermeability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimVoltageImpulse`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.DimVolumeMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.IdealToroidalWinding`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.IsAlignedParamagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.IsThinCircularTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.SatisfiesExternalSourceWorkLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.SatisfiesFaradayCompensationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.SatisfiesParamagneticConstitutiveLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.SatisfiesThinTorusAmpereLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.TorusGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_2.UniformMagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
