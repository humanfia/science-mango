# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_4_B_4.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_B_4.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1ed9eeb2a0df5214a11c7730e2f6d4b93fc8f3c38f5c6ad23ce3013984522708
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `DimLength`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `DimVolume`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `InnerProductSpace.volume_ball_of_dim_even` | module `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` | package Mathlib | **Volume of an Even-Dimensional Ball.** In a real inner product space $E$ of even dimension $n = 2k$, the volume of an open ball of radius $r$ centered at any point $x \in E$ is given by $$ \text{vol}(B(x, r)) = r^{2k...
- `MeasureTheory.tacticVolume_tac` | module `Mathlib.MeasureTheory.Measure.MeasureSpaceDef` | package Mathlib | The tactic `exact volume`, to be used in optional (`autoParam`) arguments.

### Query: `pressureInPascals`
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `lengthInMeters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `areaInSquareMeters`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `DimArea.squareMile_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **The SI Value of a Square Mile.** The area of one square mile, when expressed in International System of Units (SI) base units (square meters), is exactly $2,589,988.110336$.

### Query: `volumeInCubicMeters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.

### Query: `temperatureInKelvin`
- `TemperatureUnit.kelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The definition of a temperature unit of kelvin.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `Figure19CylinderGeometry`
- `AlgebraicGeometry.AlgebraicCycle` | module `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic` | package Mathlib | Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z` with locally finite support (see the module docstring for more details). Note: currently this is an abbrev to save som...
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `HomotopicalAlgebra.Cylinder.ofFactorizationData` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | A cylinder object for `A` can be obtained from a factorization of the obvious map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration.

### Query: `PreviousPartB3Readout`
- `Part` | module `Mathlib.Data.Part` | package Mathlib | `Part α` is the type of "partial values" of type `α`. It is similar to `Option α` except the domain condition can be an arbitrary proposition, not necessarily decidable.
- `Mathlib.Command.MinImports.previousInstName` | module `Mathlib.Tactic.MinImports` | package Mathlib | `previousInstName nm` takes as input a name `nm`, assuming that it is the name of an auto-generated "nameless" `instance`. If `nm` ends in `..._n`, where `n` is a number, it returns the same name, but with `_n` replac...
- `Part.some` | module `Mathlib.Data.Part` | package Mathlib | The `some a` value in `Part` has a `True` domain and the function returns `a`.

### Query: `DryAirWaterVaporExperiment`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `εNFA.evalFrom` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element of `S`.

## Grounded Mathlib/PhysLean names

- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `InnerProductSpace.volume_ball_of_dim_even` (Mathlib)
- `MeasureTheory.tacticVolume_tac` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `DimArea.squareMile_in_SI` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `TemperatureUnit.kelvin` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `AlgebraicGeometry.AlgebraicCycle` (Mathlib)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `HomotopicalAlgebra.Cylinder.ofFactorizationData` (Mathlib)
- `Part` (Mathlib)
- `Mathlib.Command.MinImports.previousInstName` (Mathlib)
- `Part.some` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `εNFA.evalFrom` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_4_B_4.ClausiusClapeyronData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.DimVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.DryAirWaterVaporExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.Figure19CylinderGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.PreviousPartB3Readout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_4_B_4.SatisfiesClausiusClapeyron`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
