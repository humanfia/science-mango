# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8b4ea0f4f1b39e7f922e779e980fa3394481b37ad1149c3b160e53c149cb28f0
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `electricCurrentDimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `magneticFieldStrengthDimension`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `vacuumPermeabilityDimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Electromagnetism.FreeSpace.ε₀_ne_zero` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | **Non-zero Vacuum Permittivity.** In any free space, the vacuum permittivity $\varepsilon_0$ is non-zero.

### Query: `magneticFluxDensityDimension`
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `PhysicalLength`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `Dimension.L𝓭_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Component.** The length component of the fundamental physical dimension for length is equal to 1.

### Query: `PhysicalArea`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `PhysicalVolume`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `ElectricCurrentMagnitude`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.CurrentDensity` | module `Physlib.Electromagnetism.Basic` | package PhysLean | Current density.
- `Electromagnetism.ElectromagneticPotential.canonicalMomentum_eq_electricField` | module `Physlib.Electromagnetism.Dynamics.Hamiltonian` | package PhysLean | **Canonical Momentum in Terms of the Electric Field.** For an electromagnetic potential $A$ of class $C^2$ in free space with magnetic permeability $\mu_0$ and speed of light $c$, the canonical momentum associated wit...

### Query: `MagneticFieldStrengthMagnitude`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Magnetic Field Components as Field Strength Matrix Elements.** For an electromagnetic potential $A$ that is differentiable over $\mathbb{R}$, the $i$-th spatial component of the magnetic field $\mathbf{B}$ at time $...
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Spatial Components of the Electromagnetic Field Strength Matrix.** For an electromagnetic potential $A$ and a given speed of light $c$, the spatial-spatial components of the field strength matrix at a spacetime poin...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Electromagnetism.FreeSpace.ε₀_ne_zero` (PhysLean)
- `Electromagnetism.MagneticField` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Dimension` (PhysLean)
- `Dimension.L𝓭_length` (PhysLean)
- `DimArea` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Orientation.volumeForm` (Mathlib)
- `Dimension` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.CurrentDensity` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.canonicalMomentum_eq_electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_A_1.ElectricCurrentMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.EnergyTransferSignConvention`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.HasFigure3aGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.HasNonnegativeMagnitudes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.HasStatedMaterialProperties`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.HasStatedWindingProperties`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.IsThinToroidAtScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.MagneticFieldStrengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.MagneticFluxDensityMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.MagnetizationMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.PhysicalArea`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.PhysicalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.PhysicalVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.SatisfiesParamagneticConstitutiveLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.SatisfiesToroidalAmpereCircuitalLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ToroidalAmpereReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ToroidalMagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ToroidalWinding`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.UsesUniformParallelFieldApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.VacuumPermeabilityMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
