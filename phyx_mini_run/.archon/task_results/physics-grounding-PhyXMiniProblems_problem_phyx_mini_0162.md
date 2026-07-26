# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0162.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0162.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4947de15c07222758d6f796cc3b1382bda64001869c87a96c878967bd871d1d3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Plane`
- `Complex.isOpen_slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | **Openness of the Slit Plane.** The slit plane, defined as the set of complex numbers $z$ such that $\text{Re}(z) > 0$ or $\text{Im}(z) \neq 0$, is an open subset of the complex plane.
- `EuclideanGeometry.orthogonalProjection` | module `Mathlib.Geometry.Euclidean.Projection` | package Mathlib | The orthogonal projection of a point onto a nonempty affine subspace.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `metres`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `MetricSpace` | module `Mathlib.Topology.MetricSpace.Defs` | package Mathlib | A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying `dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality `dist x z ≤ dist x y + dist y z`. See pseudometric...

### Query: `length In Metres`
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.chains` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a chain (20.1168 meters)
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `physical Distance`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Nat.instDist` | module `Mathlib.Topology.Instances.Nat` | package Mathlib | **Distance on Natural Numbers.** The distance between two natural numbers $x$ and $y$ is defined as the standard distance between them when they are considered as real numbers, denoted by $\text{dist}(x, y)$.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Finite Plane Mirror`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `CategoryTheory.Limits.ReflectsFiniteProducts` | module `Mathlib.CategoryTheory.Limits.Preserves.Finite` | package Mathlib | A functor `F` preserves finite products if it reflects limits of shape `Discrete J` for finite `J`. We require this for `J = Fin n` in the definition, then generalize to `J : Type u` in the instance.

### Query: `reflect Point`
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.
- `Polynomial.reflect` | module `Mathlib.Algebra.Polynomial.Reverse` | package Mathlib | `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (revAt N i)`. In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`. In practice, `reflect` is only used when...
- `ContinuousAffineEquiv.pointReflection_apply` | module `Mathlib.Topology.Algebra.ContinuousAffineEquiv` | package Mathlib | **Point Reflection Formula.** For any points $x$ and $y$ in an affine space over a topological ring $k$, the reflection of $y$ across the center $x$ is given by the point $(x - y) + x$.

### Query: `Corridor Mirror Setup`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.IsReflexivePair.mk'` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **Reflexive Pair Construction.** A pair of parallel morphisms $f, g: A \to B$ is a reflexive pair if there exists a morphism $s: B \to A$ such that $s \gg f = \text{id}_B$ and $s \gg g = \text{id}_B$.

### Query: `Matches Corridor Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Complex.isOpen_slitPlane` (Mathlib)
- `EuclideanGeometry.orthogonalProjection` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `MetricSpace` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.chains` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Nat.instDist` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Polynomial.mirror_mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `CategoryTheory.Limits.ReflectsFiniteProducts` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Polynomial.reflect` (Mathlib)
- `ContinuousAffineEquiv.pointReflection_apply` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.IsReflexivePair.mk'` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0162.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.CorridorMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.FinitePlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.HasUnobstructedImageRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.IsFirstVisibleDistance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.MatchesCorridorFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.ObeysFinitePlaneMirrorVisibilityLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.OpticalPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0162.UnfoldedSightLineClearsWallEdge`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
