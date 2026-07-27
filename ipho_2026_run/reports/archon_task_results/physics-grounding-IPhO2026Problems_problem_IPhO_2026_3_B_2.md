# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:fa39184ff3198222275351f079e7ee20a8bf6689d8b6dd5838e392c9735ba71c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `ThermodynamicTemperature`
- `CanonicalEnsemble.thermodynamicEntropy_def` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | **Definition of Thermodynamic Entropy.** For a canonical ensemble $\mathcal{C}$ at temperature $T$, the thermodynamic entropy is defined as the product of the negative Boltzmann constant $-k_B$ and the integral of the...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.

### Query: `PhysicalVolume`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `AppliedFieldStrengthMagnitude`
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` | module `Physlib.Electromagnetism.Kinematics.FieldStrength` | package PhysLean | The field strength from an electromagnetic potential, as a tensor `F^{μν}`.
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.FieldStrength` | package PhysLean | The matrix corresponding to the field strength in the standard basis.
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Magnetic Field Components as Field Strength Matrix Elements.** For an electromagnetic potential $A$ that is differentiable over $\mathbb{R}$, the $i$-th spatial component of the magnetic field $\mathbf{B}$ at time $...

### Query: `MagnetizationMagnitude`
- `MulArchimedeanClass.mk_right_le_mk_mul_iff` | module `Mathlib.Algebra.Order.Archimedean.Class` | package Mathlib | **Comparison of Multiplicative Archimedean Magnitudes.** In a multiplicative Archimedean class, the magnitude of an element $b$ is less than or equal to the magnitude of the product $a \cdot b$ if and only if the magn...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.

### Query: `VacuumPermeability`
- `Electromagnetism.FreeSpace.ε₀_ne_zero` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | **Non-zero Vacuum Permittivity.** In any free space, the vacuum permittivity $\varepsilon_0$ is non-zero.
- `Equiv.Perm.isCycleOn_empty` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | **Permutation Cycle on the Empty Set.** Any permutation $f$ is vacuously a cycle on the empty set.
- `Electromagnetism.EMSystem.coulombConstant` | module `Physlib.Electromagnetism.Basic` | package PhysLean | Coulomb's constant.

### Query: `CurieConstantPerMole`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `Electromagnetism.EMSystem.coulombConstant` | module `Physlib.Electromagnetism.Basic` | package PhysLean | Coulomb's constant.
- `Mathlib.Tactic.Find.findDeclsPerHead` | module `Mathlib.Tactic.Find` | package Mathlib | **Search Index for Declarations by Head Symbol.** This initialization process constructs a cache that maps the head index of a declaration's type to a list of names of all non-blacklisted declarations sharing that hea...

### Query: `LambdaPerMole`
- `DimSpeed.oneMilePerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 mile per hour.
- `Mathlib.Meta.FunProp.LambdaTheoremsExt` | module `Mathlib.Tactic.FunProp.Theorems` | package Mathlib | Environment extension storing lambda theorems.
- `Mathlib.Tactic.Find.findDeclsPerHead` | module `Mathlib.Tactic.Find` | package Mathlib | **Search Index for Declarations by Head Symbol.** This initialization process constructs a cache that maps the head index of a declaration's type to a list of names of all non-blacklisted declarations sharing that hea...

### Query: `HeatCapacityAtConstantMagnetization`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).

### Query: `temperatureInKelvin`
- `TemperatureUnit.kelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The definition of a temperature unit of kelvin.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `CanonicalEnsemble.thermodynamicEntropy_def` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Temperature` (PhysLean)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Orientation.volumeForm` (Mathlib)
- `Dimension` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` (PhysLean)
- `MulArchimedeanClass.mk_right_le_mk_mul_iff` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.FreeSpace.ε₀_ne_zero` (PhysLean)
- `Equiv.Perm.isCycleOn_empty` (Mathlib)
- `Electromagnetism.EMSystem.coulombConstant` (PhysLean)
- `LocallyConstant` (Mathlib)
- `Electromagnetism.EMSystem.coulombConstant` (PhysLean)
- `Mathlib.Tactic.Find.findDeclsPerHead` (Mathlib)
- `DimSpeed.oneMilePerHour` (PhysLean)
- `Mathlib.Meta.FunProp.LambdaTheoremsExt` (Mathlib)
- `Mathlib.Tactic.Find.findDeclsPerHead` (Mathlib)
- `LocallyConstant` (Mathlib)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `TemperatureUnit.kelvin` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_B_2.AppliedFieldStrengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.CurieConstantPerMole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.HeatCapacityAtConstantMagnetization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.LambdaPerMole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.MagnetizationMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.ParamagneticTorusProcess`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.ParamagneticTorusState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.PhysicalVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.SatisfiesParamagneticTorusLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.ThermodynamicTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.VacuumPermeability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
