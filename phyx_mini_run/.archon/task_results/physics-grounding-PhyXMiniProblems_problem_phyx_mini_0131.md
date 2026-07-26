# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0131.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0131.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6f7fcc3fbb60ffb1e1f718923008519f33a19f9eb258e6b61fcc6e71d419ccc2
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

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `arcseconds Per Degree`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `LengthUnit.parsecs` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a parsec (648,000/π astronomicalUnits).

### Query: `arcseconds To Radians`
- `Real.arcsin` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` | package Mathlib | Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`. It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`.
- `toEuclidean` | module `Mathlib.Analysis.InnerProductSpace.EuclideanDist` | package Mathlib | If `E` is a finite-dimensional space over `ℝ`, then `toEuclidean` is a continuous `ℝ`-linear equivalence between `E` and the Euclidean space of the same dimension.
- `Real.arcsin_eq_pi_div_two` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` | package Mathlib | **Arcsine Equals $\pi/2$.** For any real number $x$, the arcsine of $x$ is equal to $\pi/2$ if and only if $x \ge 1$.

### Query: `Telescope Optical Design`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `LibraryNote.Design_choices_about_smooth_algebraic_structures` | module `Mathlib.Geometry.Manifold.Algebra.Monoid` | package Mathlib | 1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend `IsManifold I n G`. This way we save users from adding both `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many...
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Observatory Location`
- `Lean.Name.location` | module `Physlib.Meta.Basic` | package PhysLean | Returns the location of a name.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.

### Query: `Resolution Limitation`
- `Cardinal.not_injective_limitation_set` | module `Mathlib.SetTheory.Ordinal.FixedPointApproximants` | package Mathlib | **Non-existence of an Injective Map from the Successor Cardinal's Initial Segment.** For any cardinal $\kappa$, there is no injective function $g$ defined on the set of ordinals strictly less than the order type of th...
- `Filter.limsup` | module `Mathlib.Order.LiminfLimsup` | package Mathlib | The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that the inequality `u x ≤ a` eventually holds for `f`.
- `TopRep.resolution` | module `Mathlib.RepresentationTheory.Homological.ContCohomology.Basic` | package Mathlib | The complex of functors whose behaviour pointwise takes an `R`-linear `G`-representation `M` to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯` The `G`-invariant submodules of it is the homogeneous cochains...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `Polynomial.degree` (Mathlib)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `LengthUnit.parsecs` (PhysLean)
- `Real.arcsin` (Mathlib)
- `toEuclidean` (Mathlib)
- `Real.arcsin_eq_pi_div_two` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `LibraryNote.Design_choices_about_smooth_algebraic_structures` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Lean.Name.location` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Cardinal.not_injective_limitation_set` (Mathlib)
- `Filter.limsup` (Mathlib)
- `TopRep.resolution` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0131.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.FigureLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.HasPhysicalResolutionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.IsNearestDisplayedImprovementChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.MatchesScenarioAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.ObservatoryLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.ResolutionLimitation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.SatisfiesRayleighCriterion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.SatisfiesResolutionImprovementLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.TelescopeOpticalDesign`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0131.TelescopeResolutionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
