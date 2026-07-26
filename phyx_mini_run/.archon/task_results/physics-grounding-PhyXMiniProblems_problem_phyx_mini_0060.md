# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0060.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0060.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e98d3764f42f9e27433e4e0e222e34db0b8ece418d11a21b9bfaf928642c720b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Plane`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `MSSMACC.planeY₃B₃` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3` | package PhysLean | The plane of linear solutions spanned by `Y₃`, `B₃` and `R`, a point orthogonal to `Y₃` and `B₃`.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `Light Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray.linearEquiv_smul_eq_map` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.map`.
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `point At`
- `OnePoint.IsZeroAt` | module `Mathlib.NumberTheory.ModularForms.BoundedAtCusp` | package Mathlib | We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is zero at `∞`.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `Pointed` | module `Mathlib.CategoryTheory.Category.Pointed` | package Mathlib | The category of pointed types.

### Query: `Plane Mirror`
- `Polynomial.mirror_smul` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Scalar Multiplication of Mirror Polynomials.** For any scalar $a$ and polynomial $p$ over a domain $R$, the mirror of the scalar product $a \cdot p$ is equal to the scalar product of $a$ and the mirror of $p$.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `reflect Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `TimeTransMan.neg` | module `Physlib.SpaceAndTime.Time.TimeTransMan` | package PhysLean | Given a `zero`, `neg zero t` is the time the same distance away from `zero` as `t` in any units but in the opposite direction.

### Query: `Mirror Deflection Setup`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `AffineEquiv.pointReflection_apply` | module `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv` | package Mathlib | **Point Reflection Formula.** For any points $x$ and $y$ in an affine space, the reflection of $y$ across the center $x$ is given by adding the displacement vector from $y$ to $x$ to the point $x$.

### Query: `Has Geometric Angle Readouts`
- `hasSum_geometric_two` | module `Mathlib.Analysis.SpecificLimits.Basic` | package Mathlib | **Sum of the Geometric Series with Ratio 1/2.** The infinite series $\sum_{n=0}^{\infty} \left(\frac{1}{2}\right)^n$ converges to $2$.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `EuclideanGeometry.Sphere.two_zsmul_oangle_eq` | module `Mathlib.Geometry.Euclidean.Angle.Sphere` | package Mathlib | Oriented angle version of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result), represented here as equality of t...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `MSSMACC.planeY₃B₃` (PhysLean)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray.linearEquiv_smul_eq_map` (Mathlib)
- `Module.Ray` (Mathlib)
- `OnePoint.IsZeroAt` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `Pointed` (Mathlib)
- `Polynomial.mirror_smul` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `TimeTransMan.neg` (PhysLean)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `AffineEquiv.pointReflection_apply` (Mathlib)
- `hasSum_geometric_two` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `EuclideanGeometry.Sphere.two_zsmul_oangle_eq` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0060.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.HasGeometricAngleReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.LightRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.MatchesAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.MirrorDeflectionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.ObeysSpecularReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.Plane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0060.PlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
