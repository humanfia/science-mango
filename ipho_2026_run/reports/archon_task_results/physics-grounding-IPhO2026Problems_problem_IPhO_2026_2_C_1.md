# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:0e23e7bea8aad26fc7a79b90f414f9bf669a8849fcb92426da92512ddbd56c26
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `PlanePoint`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Configuration.ProjectivePlane.pointCount_eq_pointCount` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | **Equality of Point Counts on Lines.** In a finite projective plane, every pair of lines is incident to the same number of points.
- `coplanar_singleton` | module `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` | package Mathlib | A single point is coplanar.

### Query: `HalfCylindricalMirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `HomotopicalAlgebra.Precylinder.symm` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | The precylinder object obtained by switching the two inclusions.

### Query: `SlopeInterceptRay`
- `slope` | module `Mathlib.LinearAlgebra.AffineSpace.Slope` | package Mathlib | `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval `[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`.
- `map_lt_lineMap_iff_slope_lt_slope_right` | module `Mathlib.LinearAlgebra.AffineSpace.Ordered` | package Mathlib | Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly below the segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`.
- `lineMap_slope_lineMap_slope_lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.Slope` | package Mathlib | `slope f a b` is an affine combination of `slope f a (lineMap a b r)` and `slope f (lineMap a b r) b`. We use `lineMap` to express this property.

### Query: `OnUpperHalfMirror`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `UpperHalfPlane.ofComplex_apply` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Topology` | package Mathlib | **Left Inverse of the Upper Half-Plane Inclusion.** For any element $z$ in the upper half-plane $\mathbb{H}$, applying the map `ofComplex` to the complex number $z$ (viewed as an element of $\mathbb{C}$) returns the o...
- `UpperHalfPlane.ofComplex` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Topology` | package Mathlib | A section `ℂ → ℍ` of the natural inclusion map, bundled as an `OpenPartialHomeomorph`.

### Query: `LiesOnRayLine`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `norm_injOn_ray_right` | module `Mathlib.Analysis.Normed.Module.Ray` | package Mathlib | **Injectivity of the Norm on a Ray.** For any non-zero vector $y$, the norm function is injective when restricted to the set of vectors $x$ that lie on the same ray as $y$.

### Query: `ObeysSpecularReflection`
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Plane Point`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Configuration.ProjectivePlane.pointCount_eq_pointCount` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | **Equality of Point Counts on Lines.** In a finite projective plane, every pair of lines is incident to the same number of points.
- `coplanar_singleton` | module `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` | package Mathlib | A single point is coplanar.

### Query: `Half Cylindrical Mirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `HomotopicalAlgebra.Precylinder.symm` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | The precylinder object obtained by switching the two inclusions.

### Query: `Slope Intercept Ray`
- `slope` | module `Mathlib.LinearAlgebra.AffineSpace.Slope` | package Mathlib | `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval `[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`.
- `map_lt_lineMap_iff_slope_lt_slope_right` | module `Mathlib.LinearAlgebra.AffineSpace.Ordered` | package Mathlib | Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly below the segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`.
- `Function.Injective.sameRay_map_iff` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The images of two vectors under an injective linear map are on the same ray if and only if the original vectors are on the same ray.

## Grounded Mathlib/PhysLean names

- `UpperHalfPlane` (Mathlib)
- `Configuration.ProjectivePlane.pointCount_eq_pointCount` (Mathlib)
- `coplanar_singleton` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `HomotopicalAlgebra.Precylinder.symm` (Mathlib)
- `slope` (Mathlib)
- `map_lt_lineMap_iff_slope_lt_slope_right` (Mathlib)
- `lineMap_slope_lineMap_slope_lineMap` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `UpperHalfPlane.ofComplex_apply` (Mathlib)
- `UpperHalfPlane.ofComplex` (Mathlib)
- `SameRay` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `norm_injOn_ray_right` (Mathlib)
- `Module.reflection` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Configuration.ProjectivePlane.pointCount_eq_pointCount` (Mathlib)
- `coplanar_singleton` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `HomotopicalAlgebra.Precylinder.symm` (Mathlib)
- `slope` (Mathlib)
- `map_lt_lineMap_iff_slope_lt_slope_right` (Mathlib)
- `Function.Injective.sameRay_map_iff` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_C_1.HalfCylindricalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.LiesOnRayLine`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.ObeysSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.OnUpperHalfMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.PlanePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.SlopeInterceptRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
