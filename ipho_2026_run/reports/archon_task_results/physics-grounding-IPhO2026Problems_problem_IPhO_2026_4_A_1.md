# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_A_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_A_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:545dbff28daef5c4ba93ebc3e94bf2c3e874df60746640c181b3815ba8d9b011
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

### Query: `Mass`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `MassDensity`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `AbsoluteTemperature`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `TemperatureUnit.absoluteFahrenheit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees fahrenheit ((5/9) of a kelvin). Note, this is fahrenheit starting at `0` absolute temperature.
- `abs` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | `abs a`, denoted `|a|`, is the absolute value of `a`

### Query: `Pressure`
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `NVEHamiltonian.pressure` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.ThermoQuantities` | package PhysLean | Pressure, as a function of T. Defined as the conjugate variable to volume.

### Query: `siValue`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `DimArea.are_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of an Are in SI Units.** In the SI unit system, the value of one are is exactly 100.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

### Query: `SubstanceCountingModel`
- `ValueDistribution.logCounting` | module `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic` | package Mathlib | The logarithmic counting function of a meromorphic function. If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logarithmically weighted measure of the number of times the function `f` takes a g...
- `Nat.primeCounting'` | module `Mathlib.NumberTheory.PrimeCounting` | package Mathlib | A variant of the traditional prime counting function which gives the number of primes *strictly* less than the input. More convenient for avoiding off-by-one errors. With `open scoped Nat.Prime`, this has notation `π'`.
- `Subtype.countable` | module `Mathlib.Data.Countable.Defs` | package Mathlib | **Countability of Subtypes.** Any subtype of a countable type is itself countable.

### Query: `ConfinedAirState`
- `CongrState` | module `Mathlib.Tactic.CongrExclamation` | package Mathlib | **Congruence Tactic State.** A structure representing the state of a congruence-based decomposition process, consisting of a collection of unresolved goals (metavariables) that the procedure could not automatically di...
- `Turing.TM0to1.Λ'.act` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Action State Constructor.** An action state is defined as a state in the emulating machine that represents the intermediate process of executing a specific Turing machine statement and then transitioning to a given...
- `FluidDynamics.FluidState` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | The density and velocity fields of a fluid on `d`-dimensional space.

### Query: `Figure17Geometry`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` | module `Mathlib.Geometry.Euclidean.Angle.Sphere` | package Mathlib | **Thales' theorem**: For three distinct points, the angle at the second point is a right angle if and only if the second point lies on the sphere having the first and third points as diameter endpoints.

## Grounded Mathlib/PhysLean names

- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `FluidDynamics.MassDensity` (PhysLean)
- `MassUnit` (PhysLean)
- `Temperature` (PhysLean)
- `TemperatureUnit.absoluteFahrenheit` (PhysLean)
- `abs` (Mathlib)
- `DimPressure` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `NVEHamiltonian.pressure` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `DimArea.are_in_SI` (PhysLean)
- `UnitChoices.SI_charge` (PhysLean)
- `ValueDistribution.logCounting` (Mathlib)
- `Nat.primeCounting'` (Mathlib)
- `Subtype.countable` (Mathlib)
- `CongrState` (Mathlib)
- `Turing.TM0to1.Λ'.act` (Mathlib)
- `FluidDynamics.FluidState` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_A_1.AbsoluteTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.ConfinedAirState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.ExperimentalConditions`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.Figure17Geometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.GoverningLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.IsochoricAirSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.Length`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.Mass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.MassDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.MatchesOfficialSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.PhysicalAdmissibility`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.Pressure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.ScalarEstimate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.SourceReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.SubstanceCountingModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_A_1.WithinEstimate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
