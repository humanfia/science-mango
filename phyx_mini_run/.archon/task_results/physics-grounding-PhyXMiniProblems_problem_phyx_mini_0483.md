# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0483.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0483.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Absolute Temperature Quantity`
- `TemperatureUnit.absoluteFahrenheit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees fahrenheit ((5/9) of a kelvin). Note, this is fahrenheit starting at `0` absolute temperature.
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `TemperatureUnit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The choices of translationally-invariant metrics on the temperature-manifold. Such a choice corresponds to a choice of units for temperature.

### Query: `Linear Expansion Coefficient Quantity`
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `UpperHalfPlane.qExpansion` | module `Mathlib.NumberTheory.ModularForms.QExpansion` | package Mathlib | The `q`-expansion of a function on the upper half plane with strict period `h`, bundled as a `PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunction` at `q = 0`, where `q = exp(2πiτ/h)` is...
- `Mathlib.Tactic.Linarith.Linexp.zfind` | module `Mathlib.Tactic.Linarith.Datatypes` | package Mathlib | `l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `temperature In Kelvins`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `temperature In Degrees Celsius`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `expansion Coefficient Per Kelvin`
- `UpperHalfPlane.qExpansion` | module `Mathlib.NumberTheory.ModularForms.QExpansion` | package Mathlib | The `q`-expansion of a function on the upper half plane with strict period `h`, bundled as a `PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunction` at `q = 0`, where `q = exp(2πiτ/h)` is...
- `TemperatureUnit.kelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The definition of a temperature unit of kelvin.
- `PowerSeries.coeff_expand_mul` | module `Mathlib.RingTheory.PowerSeries.Expand` | package Mathlib | **Coefficient of an Expanded Power Series.** For a formal power series $\phi$ and a positive natural number $p$, the $(p \cdot m)$-th coefficient of the expansion of $\phi$ by $p$ is equal to the $m$-th coefficient of...

### Query: `Season`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `IsEllSequence` | module `Mathlib.NumberTheory.EllipticDivisibilitySequence` | package Mathlib | **Alias** of `IsEllipticSequence`. --- The proposition that a sequence indexed by `ℤ` is an elliptic sequence.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `TemperatureUnit.absoluteFahrenheit` (PhysLean)
- `Temperature` (PhysLean)
- `TemperatureUnit` (PhysLean)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `UpperHalfPlane.qExpansion` (Mathlib)
- `Mathlib.Tactic.Linarith.Linexp.zfind` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Temperature` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `MvPolynomial.degrees` (Mathlib)
- `Temperature` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `UpperHalfPlane.qExpansion` (Mathlib)
- `TemperatureUnit.kelvin` (PhysLean)
- `PowerSeries.coeff_expand_mul` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `IsEllSequence` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0483.AbsoluteTemperatureQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.EiffelTowerFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.EiffelTowerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.HasPhysicalTowerParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.IsUniqueClosestDisplayedHeightChange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.LinearExpansionCoefficientQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.MatchesEiffelTowerScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.MatchesPrimaryTowerFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.MatchesTowerReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.ObeysLinearThermalExpansion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.Season`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.StructuralIdealization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.StructuralMaterial`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0483.UsesStandardWroughtIronCalibration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
