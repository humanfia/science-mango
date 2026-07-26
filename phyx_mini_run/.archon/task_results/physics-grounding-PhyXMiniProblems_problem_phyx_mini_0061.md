# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0061.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0061.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:620156d737cc99359d5b1df13a5715a83683cc561014071075b2db4a8ea6047b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `point From Readouts`
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `OnePoint.continuous_iff_from_nat` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | **Continuity on the One-Point Compactification of the Natural Numbers.** A function $f$ from the one-point compactification of the natural numbers $\mathbb{N} \cup \{\infty\}$ to a topological space $Y$ is continuous...
- `OnePoint.continuous_iff_from_discrete` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | **Continuity on the One-Point Compactification of a Discrete Space.** Let $X$ be a topological space with the discrete topology. A function $f$ from the one-point compactification of $X$ to a topological space $Y$ is...

### Query: `horizontal Readout`
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the horizontal identity 2-square.

### Query: `downward Readout`
- `Acc.of_downward_closed` | module `Mathlib.Logic.Relation` | package Mathlib | **Accessibility under Downward-Closed Functions.** Let $f: \alpha \to \beta$ be a function and $r_\beta$ be a binary relation on $\beta$. Suppose that $f$ is downward-closed with respect to $r_\beta$, meaning that for...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Multiset.strongDownwardInduction` | module `Mathlib.Data.Multiset.Basic` | package Mathlib | Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than `n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of cardinality less than `...

### Query: `Vertical Mirror`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Reflected Light Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...

### Query: `Mirror Ray Setup`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `units_inv_smul` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Scaling by an inverse unit is the same as scaling by itself.

### Query: `left Normal Reference Point`
- `Subgroup.Normal` | module `Mathlib.Algebra.Group.Subgroup.Defs` | package Mathlib | A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` [Wikidata Q743179](https://www.wikidata.org/wiki/Q743179)
- `Mathlib.Tactic.BicategoryLike.NormalExpr.leftUnitorM` | module `Mathlib.Tactic.CategoryTheory.Coherence.Normalize` | package Mathlib | The left unitor as a term of `normalExpr`.
- `midpoint_pointReflection_left` | module `Mathlib.LinearAlgebra.AffineSpace.Midpoint` | package Mathlib | **Midpoint of a Point Reflection.** For any two points $x$ and $y$ in an affine space, the midpoint between the reflection of $y$ across $x$ and the point $y$ itself is $x$.

### Query: `Matches Mirror Ray Figure`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `OnePoint` (Mathlib)
- `OnePoint.continuous_iff_from_nat` (Mathlib)
- `OnePoint.continuous_iff_from_discrete` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` (Mathlib)
- `Acc.of_downward_closed` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Multiset.strongDownwardInduction` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `SameRay` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `units_inv_smul` (Mathlib)
- `Subgroup.Normal` (Mathlib)
- `Mathlib.Tactic.BicategoryLike.NormalExpr.leftUnitorM` (Mathlib)
- `midpoint_pointReflection_left` (Mathlib)
- `SameRay` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0061.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.FollowsSingleReflectionBranch`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.MatchesMirrorRayFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.MirrorRaySetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.ReflectedLightRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.SatisfiesLawOfReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0061.VerticalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
