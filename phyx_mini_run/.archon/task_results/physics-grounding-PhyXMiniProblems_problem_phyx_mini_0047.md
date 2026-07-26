# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0047.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0047.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4e7227af0d21625c48c6a8e36ce03d31775d56343522b1014c8596fa15c4910c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Millimeters`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `Aperture Geometry`
- `Cosmology.SpatialGeometry` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)`
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `AlgebraicGeometry.AlgebraicCycle` | module `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic` | package Mathlib | Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z` with locally finite support (see the module docstring for more details). Note: currently this is an abbrev to save som...

### Query: `Diffraction Regime`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `linter.tacticAnalysis.regressions.ringToGrind` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Debug `grind` by identifying places where it does not yet supersede `ring`.
- `linarithToGrindRegressions` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Debug `grind` by identifying places where it does not yet supersede `linarith`.

### Query: `Single Slit Apparatus`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `Pi.single` | module `Mathlib.Algebra.Notation.Pi.Basic` | package Mathlib | The function supported at `i`, with value `x` there, and `0` elsewhere.
- `Complex.starConvex_slitPlane` | module `Mathlib.Analysis.Complex.Convex` | package Mathlib | The slit plane is star-convex at a positive number.

### Query: `First Minimum Geometry`
- `List.minimum` | module `Mathlib.Data.List.MinMax` | package Mathlib | `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for `[]`
- `NNReal.min_le_agm` | module `Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean` | package Mathlib | **Minimum Bound of the Arithmetic-Geometric Mean.** For any two nonnegative real numbers $x$ and $y$, their minimum is less than or equal to their arithmetic-geometric mean: $\min(x, y) \le \operatorname{agm}(x, y)$.
- `List.trop_minimum` | module `Mathlib.Algebra.Tropical.BigOperators` | package Mathlib | **Tropicalization of the Minimum of a List.** For any list of elements in a linearly ordered set $R$, the tropicalization of the minimum of the list is equal to the sum of the tropicalized elements of the list in the...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `Cosmology.SpatialGeometry` (PhysLean)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `AlgebraicGeometry.AlgebraicCycle` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `linter.tacticAnalysis.regressions.ringToGrind` (Mathlib)
- `linarithToGrindRegressions` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `Pi.single` (Mathlib)
- `Complex.starConvex_slitPlane` (Mathlib)
- `List.minimum` (Mathlib)
- `NNReal.min_le_agm` (Mathlib)
- `List.trop_minimum` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0047.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.ApertureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.DiffractionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.FirstMinimumGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.SatisfiesFirstMinimumDiffractionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.SingleSlitApparatus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0047.UsesFraunhoferSingleSlitModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
