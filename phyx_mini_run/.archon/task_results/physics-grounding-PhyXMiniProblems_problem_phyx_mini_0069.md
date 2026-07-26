# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0069.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0069.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ebf60a95da870d6a8a87a9608011118fdc9815ba28f0aaa1e8d5288c42f5ba22
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `mirror Direction Subspace`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `AffineSubspace.direction_bot` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of `⊥` is the submodule `⊥`.
- `Submodule.toAffineSubspace_direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | **Direction of a Submodule viewed as an Affine Subspace.** For any submodule $s$ of a module $V$ over a ring $k$, the direction of the affine subspace associated with $s$ is equal to the submodule $s$ itself.

### Query: `Satisfies Specular Reflection`
- `LinearMap.IsReflective` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is injective, and for any vector `y`, the norm of `x` divides twice the inner product of `x` and `y`. These conditions are what...
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...

### Query: `Two Mirror Laser Setup`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `Polynomial.mirror_zero` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror of the Zero Polynomial.** The mirror of the zero polynomial is equal to the zero polynomial.

### Query: `Matches Two Mirror Figure`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_inj` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Injectivity of the Mirror Polynomial.** Two polynomials are equal if and only if their mirror polynomials are equal.

### Query: `Satisfies Two Mirror Reflection Laws`
- `Polynomial.mirror_eq_iff` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Mirror Symmetry of Polynomials.** For any two polynomials $p$ and $q$, the mirror of $p$ is equal to $q$ if and only if $p$ is equal to the mirror of $q$.
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `Module.invOn_reflection_of_mapsTo` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection as a Self-Inverse on a Set.** Given a module $M$ and a reflection map defined by an element $x$ and a linear form $f$ satisfying $f(x) = 2$, the reflection is its own inverse on any subset $\Phi$ of $M$.

### Query: `phi Radians`
- `Real.pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` | package Mathlib | The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from which one can derive all its properties. For explicit bounds on π, see `Mathlib/Analysis/Real/Pi/Bounds.lean`. Denoted `π`,...
- `Real.goldenRatio_irrational` | module `Mathlib.NumberTheory.Real.GoldenRatio` | package Mathlib | The golden ratio is irrational.
- `Real.goldenRatio` | module `Mathlib.NumberTheory.Real.GoldenRatio` | package Mathlib | The golden ratio `φ := (1 + √5)/2`.

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

### Query: `angle Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `AffineSubspace.direction_bot` (Mathlib)
- `Submodule.toAffineSubspace_direction` (Mathlib)
- `LinearMap.IsReflective` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Polynomial.mirror_zero` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_inj` (Mathlib)
- `Polynomial.mirror_eq_iff` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Module.invOn_reflection_of_mapsTo` (Mathlib)
- `Real.pi` (Mathlib)
- `Real.goldenRatio_irrational` (Mathlib)
- `Real.goldenRatio` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0069.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0069.MatchesTwoMirrorFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0069.SatisfiesSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0069.SatisfiesTwoMirrorReflectionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0069.TwoMirrorLaserSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
