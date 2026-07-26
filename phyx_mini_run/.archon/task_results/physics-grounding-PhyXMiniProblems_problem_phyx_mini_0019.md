# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0019.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0019.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:21295eb90275d408639de3939dcb2b1763f1c964bd90333d884c2738d92c2390
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Refractive Index Quantity`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `Composition.index` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | `c.index j` is the index of the block in the composition `c` containing `j`.
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `refractive Index Value`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `HolorIndex` | module `Mathlib.Data.Holor` | package Mathlib | `HolorIndex ds` is the type of valid index tuples used to identify an entry of a holor of dimensions `ds`.
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `radians Of Degrees`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Real.pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` | package Mathlib | The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from which one can derive all its properties. For explicit bounds on π, see `Mathlib/Analysis/Real/Pi/Bounds.lean`. Denoted `π`,...
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.

### Query: `Prism Ray Diagram`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Mathlib.Tactic.Widget.StringDiagram.stringPresenter` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | The `Expr` presenter for displaying string diagrams.

### Query: `Snell Law At Interface`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Law of sines** (sine rule), vector angle form.
- `EuclideanGeometry.law_sin` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Alias** of `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. --- **Law of sines** (sine rule), angle-at-point form.

### Query: `Total Internal Reflection At`
- `Relator.BiTotal.refl` | module `Mathlib.Logic.Relator` | package Mathlib | **Bi-totality of Reflexive Relations.** If a binary relation on a set is reflexive, then it is bi-total.
- `mdifferentiableAt_totalSpace` | module `Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable` | package Mathlib | Characterization of differentiable functions into a vector bundle. Version at a point
- `Std.Total.to_refl` | module `Mathlib.Order.Defs.Unbundled` | package Mathlib | **Totality Implies Reflexivity.** Any total binary relation is necessarily reflexive.

### Query: `Total Internal Reflection Ceases At`
- `mdifferentiableAt_totalSpace` | module `Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable` | package Mathlib | Characterization of differentiable functions into a vector bundle. Version at a point
- `GenContFract.terminatedAt_iff_s_none` | module `Mathlib.Algebra.ContinuedFractions.Translations` | package Mathlib | **Termination of a Generalized Continued Fraction.** A generalized continued fraction is terminated at index $n$ if and only if its sequence of partial numerators and denominators has no element at that index.
- `mdifferentiableWithinAt_totalSpace` | module `Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable` | package Mathlib | Characterization of differentiable functions into a vector bundle. Version at a point within a set

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Subgroup.index` (Mathlib)
- `Composition.index` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `Subgroup.index` (Mathlib)
- `HolorIndex` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Real.pi` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `SameRay` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.stringPresenter` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` (Mathlib)
- `EuclideanGeometry.law_sin` (Mathlib)
- `Relator.BiTotal.refl` (Mathlib)
- `mdifferentiableAt_totalSpace` (Mathlib)
- `Std.Total.to_refl` (Mathlib)
- `mdifferentiableAt_totalSpace` (Mathlib)
- `GenContFract.terminatedAt_iff_s_none` (Mathlib)
- `mdifferentiableWithinAt_totalSpace` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0019.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.PrismRayDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.RefractiveIndexQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.RoundsToHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.SnellLawAtInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.TotalInternalReflectionAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0019.TotalInternalReflectionCeasesAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
