# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0068.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0068.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a7a32613ec4418376785cd4a9dd4f653ab672908df4da7c342ad8a1b8b9ee3ef
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

### Query: `length In Metres`
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.chains` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a chain (20.1168 meters)
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Mirror Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Ball Color`
- `Metric.ball` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `ball x ε` is the set of all points `y` with `dist y x < ε`
- `Besicovitch.TauPackage.color` | module `Mathlib.MeasureTheory.Covering.Besicovitch` | package Mathlib | Group the balls into disjoint families, by assigning to a ball the smallest color for which it does not intersect any already chosen ball of this color.
- `Besicovitch.BallPackage` | module `Mathlib.MeasureTheory.Covering.Besicovitch` | package Mathlib | A ball package is a family of balls in a metric space with positive bounded radii.

### Query: `Finite Plane Mirror`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `CategoryTheory.Limits.ReflectsFiniteProducts` | module `Mathlib.CategoryTheory.Limits.Preserves.Finite` | package Mathlib | A functor `F` preserves finite products if it reflects limits of shape `Discrete J` for finite `J`. We require this for `J = Fin n` in the definition, then generalize to `J : Type u` in the instance.

### Query: `reflect In Mirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `Perpendicular Mirror Scene`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `AffineSubspace.mem_perpBisector_pointReflection_iff_inner_eq_zero` | module `Mathlib.Geometry.Euclidean.PerpBisector` | package Mathlib | **Perpendicular Bisector and Point Reflection.** A point $c$ lies on the perpendicular bisector of the segment connecting a point $p_1$ and its reflection across a point $p_2$ if and only if the vector from $p_2$ to $...

### Query: `apply Reflection Sequence`
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `CoxeterSystem.isReflection_of_mem_rightInvSeq` | module `Mathlib.GroupTheory.Coxeter.Inversion` | package Mathlib | **Reflections in the Right Inversion Sequence.** For any word $\omega$ in a Coxeter system, every element $t$ belonging to the right inversion sequence of $\omega$ is a reflection.

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
- `LengthUnit.links` (PhysLean)
- `LengthUnit.chains` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Metric.ball` (Mathlib)
- `Besicovitch.TauPackage.color` (Mathlib)
- `Besicovitch.BallPackage` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `CategoryTheory.Limits.ReflectsFiniteProducts` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `AffineSubspace.mem_perpBisector_pointReflection_iff_inner_eq_zero` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `CoxeterSystem.isReflection_of_mem_rightInvSeq` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0068.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.BallColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.FinitePlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.IsVisibleDoubleReflectionImage`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.IsVisibleReflectionImagePosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.IsVisibleSingleReflectionImage`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.MatchesPerpendicularMirrorFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.MirrorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.ObeysPlaneMirrorImageLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.OpticalPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0068.PerpendicularMirrorScene`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
