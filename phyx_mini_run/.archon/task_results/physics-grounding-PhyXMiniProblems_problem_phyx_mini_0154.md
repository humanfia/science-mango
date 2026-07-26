# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0154.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0154.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2255dd35cd234c9798f62b024eab6cfc26dae06c34880cb4ef8772f1bbee694f
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Temperature Interval Magnitude`
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `Temperature.ofNNReal_val` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | **Value of a Temperature from a Nonnegative Real.** For any nonnegative real number $t$, the numerical value of the temperature constructed from $t$ is equal to $t$ itself.
- `IntervalIntegrable` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these intervals is always empty, so this...

### Query: `Linear Expansion Coefficient Magnitude`
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `UpperHalfPlane.qExpansion` | module `Mathlib.NumberTheory.ModularForms.QExpansion` | package Mathlib | The `q`-expansion of a function on the upper half plane with strict period `h`, bundled as a `PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunction` at `q = 0`, where `q = exp(2πiτ/h)` is...
- `Mathlib.Tactic.Linarith.Linexp.zfind` | module `Mathlib.Tactic.Linarith.Datatypes` | package Mathlib | `l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.

### Query: `celsius Degree Unit`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `Polynomial.isUnit_iff_degree_eq_zero` | module `Mathlib.Algebra.Polynomial.FieldDivision` | package Mathlib | **Units of a Polynomial Ring.** A polynomial $p$ over a field is a unit if and only if its degree is equal to zero.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `temperature Interval Readout`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `Temperature.betaFromReal` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | Map a real `t` to the inverse temperature `β` corresponding to the temperature `Real.toNNReal t` (`max t 0`), returned as a real number.

### Query: `temperature Rise In Celsius Degrees`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Int.ceil` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `expansion Coefficient Readout`
- `UpperHalfPlane.qExpansion` | module `Mathlib.NumberTheory.ModularForms.QExpansion` | package Mathlib | The `q`-expansion of a function on the upper half plane with strict period `h`, bundled as a `PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunction` at `q = 0`, where `q = exp(2πiτ/h)` is...
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `FTheory.SU5.TenQuanta.anomalyCoefficient` | module `Physlib.StringTheory.FTheory.SU5.Quanta.TenQuanta` | package PhysLean | The anomaly coefficient of a `TenQuanta` is given by the pair of integers: `(∑ᵢ qᵢ Nᵢ, 3 * ∑ᵢ qᵢ² Nᵢ)`. The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084. The second component is fo...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `intervalIntegral` (Mathlib)
- `Temperature.ofNNReal_val` (PhysLean)
- `IntervalIntegrable` (Mathlib)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `UpperHalfPlane.qExpansion` (Mathlib)
- `Mathlib.Tactic.Linarith.Linexp.zfind` (Mathlib)
- `Polynomial.degree` (Mathlib)
- `Polynomial.isUnit_iff_degree_eq_zero` (Mathlib)
- `UnitChoices.SI_temperature` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Temperature` (PhysLean)
- `intervalIntegral` (Mathlib)
- `Temperature.betaFromReal` (PhysLean)
- `Temperature` (PhysLean)
- `Int.ceil` (Mathlib)
- `UnitChoices.SI_temperature` (PhysLean)
- `UpperHalfPlane.qExpansion` (Mathlib)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `FTheory.SU5.TenQuanta.anomalyCoefficient` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0154.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.BarHalf`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.BeamProfile`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.CenterCrackedBarSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.FigureLengthLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.IsUniqueClosestDisplayedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.LinearExpansionCoefficientMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.MatchesIntendedBarDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.MatchesStatedMeasurements`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.ObeysLinearThermalExpansion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.SatisfiesSymmetricBucklingGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.TemperatureIntervalMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0154.ThermalState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
