# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0399.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0399.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1d69a148d00dc58ed87e12402bee863a41e7419168f69783734f6f1ba5fc544c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Volume Quantity`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `pressure In Pascals`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `pressure In Kilopascals`
- `DimPressure.bar` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 bar (100,000 pascals).
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `volume In Cubic Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.

### Query: `temperature In Kelvins`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `celsius Zero In Kelvins`
- `Nat.RecursiveIn.zero` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | **The Zero Function is Recursive.** The constant function $f(n) = 0$ is recursive in any set of oracles $O$.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `TemperatureUnit.absoluteFahrenheit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees fahrenheit ((5/9) of a kelvin). Note, this is fahrenheit starting at `0` absolute temperature.

### Query: `temperature In Degrees Celsius`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `Driving Stage`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.order_eq_orderTop_of_ne_zero` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Equivalence of Hahn Series Orders for Non-zero Series.** For any non-zero Hahn series $x$, the order of $x$ is equal to its order in the sense of the extended order (where the order of the zero series is defined as...

### Query: `Gas Model`
- `FirstOrder.Language.Theory.Model` | module `Mathlib.ModelTheory.Semantics` | package Mathlib | A model of a theory is a structure in which every sentence is realized as true.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `modelWithCornersSelf` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)
- `DimPressure.bar` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `Temperature` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `Nat.RecursiveIn.zero` (Mathlib)
- `JoinedIn` (Mathlib)
- `TemperatureUnit.absoluteFahrenheit` (PhysLean)
- `MvPolynomial.degrees` (Mathlib)
- `Temperature` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.order_eq_orderTop_of_ne_zero` (Mathlib)
- `FirstOrder.Language.Theory.Model` (Mathlib)
- `IdealGas` (PhysLean)
- `modelWithCornersSelf` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0399.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.AssumesConstantTireVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.DrivingStage`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.FigureObservable`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.GasModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.HasPhysicalTireAirParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.IsUniqueClosestDisplayedPressure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.MatchesPrimaryTireFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.RoundsToDisplayedTenthKilopascal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.SatisfiesFixedSampleIdealGasLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.TireAirSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.TireAirState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.TireFigureComponent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.TireHeatingSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.TirePressureFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0399.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
