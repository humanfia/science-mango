# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_3.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6d55e63a42597c2f62a946abacc769149cdae1e73f3572476b35e0f0d9841c3e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `CarnotState`
- `CongrState` | module `Mathlib.Tactic.CongrExclamation` | package Mathlib | **Congruence Tactic State.** A structure representing the state of a congruence-based decomposition process, consisting of a collection of unresolved goals (metavariables) that the procedure could not automatically di...
- `ValueDistribution.Cartan.cartanKernel` | module `Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation` | package Mathlib | Given `f : ℂ → ℂ` and `R : ℝ`, define the Cartan kernel of integration as the function `α β ↦ log ‖f (circleMap 0 R β) - circleMap 0 1 α‖`.
- `Bool.carry` | module `Mathlib.Data.Bool.Basic` | package Mathlib | `carry x y c` is `x && y || x && c || y && c`.

### Query: `CarnotState.next`
- `StateTransition.Reaches₀.tail` | module `Mathlib.Computability.StateTransition` | package Mathlib | **Extension of Reachable States.** If a state $b$ is reachable from a state $a$ through zero or more applications of a transition function $f$, and a state $c$ is a possible next state from $b$ (i.e., $c \in f(b)$), t...
- `StateTransition.Reaches₀.tail'` | module `Mathlib.Computability.StateTransition` | package Mathlib | **Extension of a Reachable Path.** If a state $b$ is reachable from a state $a$ in zero or more steps under the transition function $f$, and a state $c$ is a possible next state from $b$ (i.e., $c \in f(b)$), then $c$...
- `List.next` | module `Mathlib.Data.List.Cycle` | package Mathlib | Given an element `x : α` of `l : List α` such that `x ∈ l`, get the next element of `l`. This works from head to tail, (including a check for last element) so it will match on first hit, ignoring later duplicates. For...

### Query: `Temperature`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Temperature.instZero` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | **Zero Temperature.** The type of temperatures has a zero element, defined as the temperature with a value of $0$.

### Query: `Volume`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `MassDensity`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `SpecificHeatCapacity`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).
- `Lean.Meta.DiscrTree.keysSpecific` | module `Mathlib.Lean.Meta.DiscrTree` | package Mathlib | Check if a `keys : Array DiscTree.Key` is "specific", i.e. something other than `[*]` or `[=, *, *, *]`.

### Query: `MagneticFieldStrength`
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Magnetic Field Components as Field Strength Matrix Elements.** For an electromagnetic potential $A$ that is differentiable over $\mathbb{R}$, the $i$-th spatial component of the magnetic field $\mathbf{B}$ at time $...
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **Spatial Components of the Electromagnetic Field Strength Matrix.** For an electromagnetic potential $A$ and a given speed of light $c$, the spatial-spatial components of the field strength matrix at a spacetime poin...

### Query: `Magnetization`
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `Electromagnetism.ElectromagneticPotential.magneticField_curl_eq_magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | **The Curl of the Magnetic Field and the Magnetic Field Matrix.** For a twice-differentiable electromagnetic potential $A$ and a given time $t$, the $i$-th component of the curl of the magnetic field $\mathbf{B}$ is e...

### Query: `Energy`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `CongrState` (Mathlib)
- `ValueDistribution.Cartan.cartanKernel` (Mathlib)
- `Bool.carry` (Mathlib)
- `StateTransition.Reaches₀.tail` (Mathlib)
- `StateTransition.Reaches₀.tail'` (Mathlib)
- `List.next` (Mathlib)
- `Temperature` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Temperature.instZero` (PhysLean)
- `Real.volume_real_Ico` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `FluidDynamics.MassDensity` (PhysLean)
- `MassUnit` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `Lean.Meta.DiscrTree.keysSpecific` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField_coord_eq_fieldStrengthMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField_curl_eq_magneticFieldMatrix` (PhysLean)
- `DimEnergy` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finpartition.energy` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_C_3.CarnotState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.Energy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.GoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.HasSuppliedData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.MagneticFieldStrength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.MagneticPermeability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.Magnetization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.MassDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.PreviousPartResults`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.Setup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.SpecificHeatCapacity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.Temperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_3.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
