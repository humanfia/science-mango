# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_3.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8fae692b0ec2558d98aca1f8559a071fd04740987421e34cd6b08db3166dfc45
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Figure2gMirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.

### Query: `Figure2gPoint`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Figure2gMirror.OnReflectingSurface`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `ContinuousOn` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A function between topological spaces is continuous on a subset `s` when it's continuous at every point of `s` within `s`.
- `Module.invOn_reflection_of_mapsTo` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection as a Self-Inverse on a Set.** Given a module $M$ and a reflection map defined by an element $x$ and a linear form $f$ satisfying $f(x) = 2$, the reflection is its own inverse on any subset $\Phi$ of $M$.

### Query: `ReflectedRayLine`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.

### Query: `ReflectedRayLine.Contains`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `AffineMap.lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.

### Query: `IsNeighboringReflectedIntersection`
- `IsOpen` | module `Mathlib.Topology.Defs.Basic` | package Mathlib | `IsOpen s` means that `s` is open in the ambient topological space on `X`
- `inter_mem_nhdsWithin` | module `Mathlib.Topology.NhdsWithin` | package Mathlib | **Intersection of a Set and a Neighborhood in the Neighborhood Filter Within that Set.** If $t$ is a neighborhood of a point $a$, then the intersection $s \cap t$ is a neighborhood of $a$ within the set $s$.
- `IsNoetherian` | module `Mathlib.RingTheory.Noetherian.Defs` | package Mathlib | `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module, implemented as the predicate that all `R`-submodules of `M` are finitely generated.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Figure2g Mirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.

### Query: `Figure2g Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `On Reflecting Surface`
- `ContinuousOn` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A function between topological spaces is continuous on a subset `s` when it's continuous at every point of `s` within `s`.
- `Monovary.monovaryOn` | module `Mathlib.Order.Monotone.Monovary` | package Mathlib | **Monovariation on a Subset.** If a function $f$ monovaries with a function $g$ over their entire domain, then $f$ also monovaries with $g$ on any subset $s$ of that domain.
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...

## Grounded Mathlib/PhysLean names

- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `ContinuousOn` (Mathlib)
- `Module.invOn_reflection_of_mapsTo` (Mathlib)
- `SameRay` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `RayVector` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `AffineMap.lineMap` (Mathlib)
- `IsOpen` (Mathlib)
- `inter_mem_nhdsWithin` (Mathlib)
- `IsNoetherian` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `ContinuousOn` (Mathlib)
- `Monovary.monovaryOn` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_C_3.Figure2gMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.Figure2gMirror.OnReflectingSurface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.Figure2gPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.IsNeighboringReflectedIntersection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.ReflectedRayLine`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.ReflectedRayLine.Contains`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
