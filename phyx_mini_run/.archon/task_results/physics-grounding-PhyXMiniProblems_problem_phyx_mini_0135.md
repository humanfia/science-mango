# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0135.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0135.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Beam Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `openSegment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when the base semiring has some element between `0` and `1`.
- `image_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Image of a Line Segment under an Affine Map.** For any affine map $f$ and any two points $a$ and $b$ in its domain, the image of the line segment connecting $a$ and $b$ is equal to the line segment connecting the im...

### Query: `medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` | module `Mathlib.CategoryTheory.Abelian.Preradical.Colon` | package Mathlib | **The Middle Object of the Short Complex Associated with a Preradical.** For any object $X$ in a category $\mathcal{C}$, the middle object (at index 2) of the short complex associated with a preradical is defined as t...

### Query: `Pool Search Setup`
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `Mathlib.Tactic.Find.«command#find_»` | module `Mathlib.Tactic.Find` | package Mathlib | `#find t` finds definitions and theorems whose result type matches the term `t`, and prints them as info lines. Use holes in `t` to indicate arbitrary subexpressions, for example `#find _ ∧ _` will match any conjuncti...

### Query: `incidence Angle Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `Real.Angle.toReal_le_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Upper Bound of the Real Representative of an Angle.** For any angle $\theta$, its representative in the interval $(-\pi, \pi]$ is always less than or equal to $\pi$.
- `IncidenceAlgebra` | module `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra` | package Mathlib | The `𝕜`-incidence algebra over `α`.

### Query: `refraction Angle Radians`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.toReal_eq_pi_div_two_iff` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Angle Representative Equal to $\pi/2$.** For any angle $\theta$, the unique representative of $\theta$ in the interval $(-\pi, \pi]$ is equal to $\pi/2$ if and only if $\theta$ is the angle $\pi/2$.
- `Real.Angle` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The type of angles

### Query: `Matches Pool Figure And Readouts`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `segment` (Mathlib)
- `openSegment` (Mathlib)
- `image_segment` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `Mathlib.Tactic.Find.«command#find_»` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `Real.Angle.toReal_le_pi` (Mathlib)
- `IncidenceAlgebra` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.toReal_eq_pi_div_two_iff` (Mathlib)
- `Real.Angle` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0135.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.BeamSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.HasPhysicalPoolOpticsParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.MatchesPoolFigureAndReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.PoolSearchSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.SatisfiesPlanarPoolRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.SatisfiesSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0135.UsesStandardAirWaterIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
