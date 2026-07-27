# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_1_A_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_A_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:78431e8769cda0fbfca20feffc2f5efdb49e97fc665dc69a147b635bc0bcee2b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `LengthSI`
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `AreaSI`
- `DimArea.squareMile_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **The SI Value of a Square Mile.** The area of one square mile, when expressed in International System of Units (SI) base units (square meters), is exactly $2,589,988.110336$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimArea.hectare_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Hectare in SI Units.** In the SI unit system, the value of one hectare is exactly $10,000$.

### Query: `VolumeSI`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

### Query: `MassDensitySI`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.

### Query: `AccelerationSI`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.

### Query: `PressureSI`
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimPressure.bar` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 bar (100,000 pascals).

### Query: `ForceSI`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

### Query: `TorqueSI`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimPressure.torr` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure).

### Query: `FigurePointLabel`
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `UnitChoices.SI_length` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `LengthUnit` (PhysLean)
- `DimArea.squareMile_in_SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimArea.hectare_in_SI` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `UnitChoices.SI_length` (PhysLean)
- `UnitChoices.SI_charge` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `UnitChoices.SI_mass` (PhysLean)
- `FluidDynamics.MassDensity` (PhysLean)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `DimPressure` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimPressure.bar` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `UnitChoices.SI_charge` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimPressure.torr` (PhysLean)
- `OnePoint` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Equiv.pointReflection` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_1_A_1.AccelerationSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.AreaSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.AxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.Figure1aGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.FigurePointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.ForceSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.GateConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.HingeFriction`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.HydrostaticGateLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.HydrostaticGateState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.LengthSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.MassDensitySI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.MatchesFigure1a`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.MatchesProblemSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.PressureSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.ReservoirFluid`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.RoundsToNearestCentimeterSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.SubmersionStatus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.TorqueSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.VolumeSI`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_A_1.WallOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
