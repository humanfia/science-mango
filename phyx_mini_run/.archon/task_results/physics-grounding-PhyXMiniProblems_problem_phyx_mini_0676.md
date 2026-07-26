# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0676.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0676.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:28d7621636a631976bc4d6327144557e59ac8e72669124606bb89702cce395e7
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

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Survey Point`
- `CategoryTheory.GrothendieckTopology.Point` | module `Mathlib.CategoryTheory.Sites.Point.Basic` | package Mathlib | Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)` consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements` is initially small (which allows defining the fiber...
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `River Bank Side`
- `AffineSubspace.SSameSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are strictly on the same side of `s`.
- `AffineSubspace.SOppSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are strictly on opposite sides of `s`.
- `AffineSubspace.SOppSide.not_sSameSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | **Strictly Opposite Sides are not Strictly on the Same Side.** If two points $x$ and $y$ lie strictly on opposite sides of an affine subspace $s$, then they do not lie strictly on the same side of $s$.

### Query: `River Survey Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Matches Primary River Survey Figure`
- `Ideal.primaryComponent` | module `Mathlib.Algebra.Module.Torsion.PrimaryComponent` | package Mathlib | The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`.
- `Submodule.IsPrimary` | module `Mathlib.RingTheory.IsPrimary` | package Mathlib | A proper submodule `S : Submodule R M` is primary iff `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`. This generalizes `Ideal.IsPrimary`.
- `Ideal.IsPrimary` | module `Mathlib.RingTheory.Ideal.IsPrimary` | package Mathlib | A proper ideal `I` is primary as a submodule.

### Query: `Has Physical River Survey Configuration`
- `Configuration.HasPoints` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of lines has an intersection point.
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Configuration.HasLines` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of points has a line through them.

### Query: `Matches Problem Measurements`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...

### Query: `Satisfies Right Triangle Tangent Law`
- `EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle` | package Mathlib | The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals the opposite side.
- `tangentMap_prod_right` | module `Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions` | package Mathlib | **Tangent Map of the Right Inclusion.** For a fixed point $x_0$ in a manifold $M$, the tangent map of the inclusion $y \mapsto (x_0, y)$ from a manifold $M'$ into the product manifold $M \times M'$, applied to a tange...
- `Orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals the opposite side.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `CategoryTheory.GrothendieckTopology.Point` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `AffineSubspace.SSameSide` (Mathlib)
- `AffineSubspace.SOppSide` (Mathlib)
- `AffineSubspace.SOppSide.not_sSameSide` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Ideal.primaryComponent` (Mathlib)
- `Submodule.IsPrimary` (Mathlib)
- `Ideal.IsPrimary` (Mathlib)
- `Configuration.HasPoints` (Mathlib)
- `HasSum` (Mathlib)
- `Configuration.HasLines` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two` (Mathlib)
- `tangentMap_prod_right` (Mathlib)
- `Orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0676.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.HasPhysicalRiverSurveyConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.IsUniqueClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.MatchesPrimaryRiverSurveyFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.MatchesProblemMeasurements`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.RiverBankSide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.RiverSurveySetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.SatisfiesRightTriangleTangentLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0676.SurveyPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
