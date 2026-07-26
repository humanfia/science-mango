# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0095.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0095.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d3068ac11067e240b35ab4c718bd4d90176b6347259f21ad8b00e8168c604220
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

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Interface Model`
- `modelWithCornersSelf` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace.
- `Manifold.Elab.findModel` | module `Mathlib.Geometry.Manifold.Notation` | package Mathlib | Try to find a `ModelWithCorners` instance on a type (represented by an expression `e`), using the local context to infer the appropriate instance. This supports all `ModelWithCorners` instances that are currently defi...
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` | module `Mathlib.Tactic.Widget.LibraryRewrite` | package Mathlib | The structure with all data necessary for rendering a rewrite suggestion

### Query: `Line Shift Refraction Setup`
- `AffineSubspace.shift` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Shift` | package Mathlib | `AffineSubspace.shift s c r` is an affine subspace parallel to `s`, where an arbitrary point on `s` is moved towards `c` with linear interpolation by `r`. When `r = 0`, that point is moved onto `c`. When `r = 1`, that...
- `AffineMap.lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.

### Query: `Matches Water Glass Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Has Physical Refraction Configuration`
- `Configuration.HasPoints` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of lines has an intersection point.
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `Satisfies Line Shift Geometry`
- `AffineMap.lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.
- `PureU1.Even.lineInCubicPerm_last_cond` | module `Physlib.QFT.QED.AnomalyCancellation.Even.LineInCubic` | package PhysLean | **Condition for the Final Line in a Cubic Permutation.** For any linear solution $S$ of the system $PureU1(2(n+2))$ that satisfies the cubic permutation property, the triple of values $(S_{evenShiftSnd(n)}, S_{evenShi...
- `PureU1.Even.lineInCubicPerm_last_perm` | module `Physlib.QFT.QED.AnomalyCancellation.Even.LineInCubic` | package PhysLean | **Line in Cubic Permutation Implies Line in Plane Condition.** For any linear solution $S$ of the group $U(1)^{2(n+2)}$, if $S$ satisfies the "line in cubic permutation" property, then it necessarily satisfies the "li...

### Query: `Satisfies Water To Air Snell Law`
- `Sat.Valuation.satisfies_fmla` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation. A formula is satisfied if all clauses in it are satisfied.
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `PolynomialLaw.toFun` | module `Mathlib.RingTheory.PolynomialLaw.Basic` | package Mathlib | The extension of `PolynomialLaw.toFun'` to all universes.

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
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `modelWithCornersSelf` (Mathlib)
- `Manifold.Elab.findModel` (Mathlib)
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` (Mathlib)
- `AffineSubspace.shift` (Mathlib)
- `AffineMap.lineMap` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `Configuration.HasPoints` (Mathlib)
- `HasSum` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `AffineMap.lineMap` (Mathlib)
- `PureU1.Even.lineInCubicPerm_last_cond` (PhysLean)
- `PureU1.Even.lineInCubicPerm_last_perm` (PhysLean)
- `Sat.Valuation.satisfies_fmla` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `PolynomialLaw.toFun` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0095.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.HasPhysicalRefractionConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.InterfaceModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.IsUniqueClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.LineShiftRefractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.MatchesPrimaryFigureScaleReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.MatchesWaterGlassFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.SatisfiesLineShiftGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0095.SatisfiesWaterToAirSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
