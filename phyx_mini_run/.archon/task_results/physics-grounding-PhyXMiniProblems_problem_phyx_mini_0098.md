# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0098.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0098.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:54b93db4897781281a728efd0da7828447e2d9f49cafd82a266d6f91913088c7
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dimensionless Optical Index`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `HolorIndex` | module `Mathlib.Data.Holor` | package Mathlib | `HolorIndex ds` is the type of valid index tuples used to identify an entry of a holor of dimensions `ds`.
- `Composition.index` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | `c.index j` is the index of the block in the composition `c` containing `j`.

### Query: `refractive Index Readout`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `Composition.index` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | `c.index j` is the index of the block in the composition `c` containing `j`.
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `Optical Fiber Region`
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `degree Readout`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` | module `Mathlib.Tactic.ComputeDegree` | package Mathlib | `miscomputedDegree? deg false_goals` takes as input * an `Expr`ession `deg`, representing the degree of a polynomial (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`); * a list of `MVarId`s `false_goal...
- `TuringDegree` | module `Mathlib.Computability.TuringDegree` | package Mathlib | Turing degrees are the equivalence classes of partial functions under Turing equivalence.

### Query: `Step Index Fiber Setup`
- `FiberBundleCore.Index` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | The index set of a fiber bundle core, as a convenience function for dot notation
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `SSet.stdSimplex.objMk₁_of_castSucc_lt` | module `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne` | package Mathlib | **The Value of the Standard 1-Simplex Step Function for Indices Less Than the Step. ** For any $n \in \mathbb{N}$, let $i \in \{0, \dots, n+1\}$ be the index defining a step function (an $n$-simplex of the standard $1...

### Query: `Matches Optical Fiber Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_zero` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Empty Regular Expression.** The language associated with the empty regular expression $0$ is the empty language $\emptyset$.
- `RegularExpression.matches'_star` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Kleene Star.** The language matched by the Kleene star of a regular expression $P$ is equal to the Kleene closure of the language matched by $P$.

### Query: `Is Acute Optical Angle`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Affine.Simplex.AcuteAngled` | module `Mathlib.Geometry.Euclidean.Simplex` | package Mathlib | The property of all angles of a simplex being acute.
- `Affine.Triangle.acuteAngled_iff_angle_lt` | module `Mathlib.Geometry.Euclidean.Simplex` | package Mathlib | **Acute Triangle Condition.** A triangle is acute-angled if and only if all three of its interior angles are strictly less than $\pi/2$. Specifically, for a triangle with vertices $p_0, p_1,$ and $p_2$, this condition...

### Query: `Satisfies Limiting Guidance Laws`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Subgroup.index` (Mathlib)
- `HolorIndex` (Mathlib)
- `Composition.index` (Mathlib)
- `Subgroup.index` (Mathlib)
- `Composition.index` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `Set.Ioi` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Polynomial.degree` (Mathlib)
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` (Mathlib)
- `TuringDegree` (Mathlib)
- `FiberBundleCore.Index` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `SSet.stdSimplex.objMk₁_of_castSucc_lt` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_zero` (Mathlib)
- `RegularExpression.matches'_star` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Affine.Simplex.AcuteAngled` (Mathlib)
- `Affine.Triangle.acuteAngled_iff_angle_lt` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)
- `HahnSeries.single` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0098.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.DimensionlessOpticalIndex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.IsAcuteOpticalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.MatchesNearestTenthDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.MatchesOpticalFiberFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.OpticalFiberRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.SatisfiesLimitingGuidanceLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0098.StepIndexFiberSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
