# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0024.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0024.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `Optical Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Optical Vector`
- `VectorBundle` | module `Mathlib.Topology.VectorBundle.Basic` | package Mathlib | The space `Bundle.TotalSpace F E` (for `E : B → Type*` such that each `E x` is a topological vector space) has a topological vector space structure with fiber `F` (denoted with `VectorBundle R F E`) if around every po...
- `Matrix.vecAlt1` | module `Mathlib.Data.Fin.VecNotation` | package Mathlib | `vecAlt1 v` gives a vector with half the length of `v`, with only alternate elements (odd-numbered).
- `List.Vector.scanl` | module `Mathlib.Data.Vector.Basic` | package Mathlib | Construct a `Vector β (n + 1)` from a `Vector α n` by scanning `f : β → α → β` from the "left", that is, from 0 to `Fin.last n`, using `b : β` as the starting value.

### Query: `horizontal Mirror Tangent`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `TangentSpace` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | The tangent space at a point of the manifold `M`. It is just `E`. We could use instead `(tangentBundleCore I M).toFiberBundleCore.fiber x`, but we use `E` to help the kernel. The definition of `TangentSpace` is not re...
- `Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Tangent of Complementary Angles.** For any two angles $\theta$ and $\psi$, if $2\theta + 2\psi = \pi$, then the tangent of $\psi$ is equal to the reciprocal of the tangent of $\theta$.

### Query: `vertical Mirror Tangent`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `TangentSpace` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | The tangent space at a point of the manifold `M`. It is just `E`. We could use instead `(tangentBundleCore I M).toFiberBundleCore.fiber x`, but we use `E` to help the kernel. The definition of `TangentSpace` is not re...
- `Orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals the opposite side, version subtracting vectors.

### Query: `unit Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.
- `Space.direction_unit_sq_sum` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Sum of Squared Components of a Unit Direction Vector.** For any direction vector $s$ in $d$ dimensions, the sum of the squares of its components is equal to $1$.

### Query: `Specular Reflection At`
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...
- `ContinuousAt` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A function between topological spaces is continuous at a point `x₀` if `f x` tends to `f x₀` when `x` tends to `x₀`.
- `Submodule.reflection_reflection` | module `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` | package Mathlib | Reflecting twice in the same subspace.

### Query: `In Open Square`
- `IsOpen` | module `Mathlib.Topology.Defs.Basic` | package Mathlib | `IsOpen s` means that `s` is open in the ambient topological space on `X`
- `Opens.mayerVietorisSquare` | module `Mathlib.Topology.Sheaves.MayerVietoris` | package Mathlib | The Mayer-Vietoris square attached to two open subsets of a topological space.
- `Opens.mayerVietorisSquare'` | module `Mathlib.Topology.Sheaves.MayerVietoris` | package Mathlib | A square consisting of opens `X₂ ⊓ X₃`, `X₂`, `X₃` and `X₂ ⊔ X₃` is a Mayer-Vietoris square.

### Query: `Open Segment Inside`
- `openSegment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when the base semiring has some element between `0` and `1`.
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `mem_openSegment_of_ne_left_right` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Interior Points of a Segment.** If a point $z$ belongs to the closed segment connecting $x$ and $y$, and $z$ is equal to neither $x$ nor $y$, then $z$ belongs to the open segment connecting $x$ and $y$.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `VectorBundle` (Mathlib)
- `Matrix.vecAlt1` (Mathlib)
- `List.Vector.scanl` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `TangentSpace` (Mathlib)
- `Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `TangentSpace` (Mathlib)
- `Orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.toDirection` (PhysLean)
- `Space.direction_unit_sq_sum` (PhysLean)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `ContinuousAt` (Mathlib)
- `Submodule.reflection_reflection` (Mathlib)
- `IsOpen` (Mathlib)
- `Opens.mayerVietorisSquare` (Mathlib)
- `Opens.mayerVietorisSquare'` (Mathlib)
- `openSegment` (Mathlib)
- `segment` (Mathlib)
- `mem_openSegment_of_ne_left_right` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0024.InOpenSquare`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OnLeftMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OnRightMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OnTopMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OpenSegmentInside`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OpticalPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.OpticalVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.SpecularReflectionAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0024.ThreeMirrorRayRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
