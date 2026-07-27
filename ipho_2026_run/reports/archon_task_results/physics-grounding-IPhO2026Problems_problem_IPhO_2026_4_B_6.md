# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_B_6.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_B_6.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:102273702412b723481707bf14a6f5c8138b2fabf0e027f4dfdadd62cbf9debe
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `energyDimension`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `specificEnergyDimension`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `Temperature`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Temperature.instZero` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | **Zero Temperature.** The type of temperatures has a zero element, defined as the temperature with a value of $0$.

### Query: `Length`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.

### Query: `Pressure`
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `NVEHamiltonian.pressure` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.ThermoQuantities` | package PhysLean | Pressure, as a function of T. Defined as the conjugate variable to volume.

### Query: `Mass`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Energy`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `SpecificEnergy`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Lean.Meta.DiscrTree.keysSpecific` | module `Mathlib.Lean.Meta.DiscrTree` | package Mathlib | Check if a `keys : Array DiscTree.Key` is "specific", i.e. something other than `[*]` or `[=, *, *, *]`.

### Query: `siReadout`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

### Query: `MolarLatentHeatEstimate`
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Valuation.inversion_estimate` | module `Mathlib.Topology.Algebra.Valued.ValuedField` | package Mathlib | **Inversion Estimate for Valuations.** Let $v$ be a valuation on a division ring $K$ taking values in a linearly ordered commutative group with zero $\Gamma_0$. For any elements $x, y \in K$ with $y \neq 0$ and any un...

## Grounded Mathlib/PhysLean names

- `DimEnergy` (PhysLean)
- `dimH` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy` (PhysLean)
- `Temperature` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Temperature.instZero` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `List.Vector.length` (Mathlib)
- `DimPressure` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `NVEHamiltonian.pressure` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `DimEnergy` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finpartition.energy` (Mathlib)
- `DimEnergy` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Lean.Meta.DiscrTree.keysSpecific` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI_charge` (PhysLean)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Valuation.inversion_estimate` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_B_6.Energy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.GoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.HasReferenceAndProcedureData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.Length`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.Mass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.MolarLatentHeatEstimate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.Pressure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.PreviousPartB5Result`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.SpecificEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.Temperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_6.VaporizationExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
