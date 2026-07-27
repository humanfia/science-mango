# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:107ddc673c831265fbb0e192df0913b47fd9bf21a3ea0cf2f642c039d29946d4
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `CrossSectionPoint`
- `crossProduct` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | The cross product of two vectors in $R^3$ for $R$ a commutative ring.
- `Projectivization.cross` | module `Mathlib.LinearAlgebra.Projectivization.Constructions` | package Mathlib | Cross product on the projective plane.
- `cross_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Vector Triple Product Identity.** For any three vectors $u, v, w \in R^3$ over a commutative ring $R$, the iterated cross product satisfies the identity $u \times (v \times w) = u \times (v \times w) - v \times (u \...

### Query: `FigureLabel`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `HalfCylindricalMirror`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `HomotopicalAlgebra.Precylinder.symm` | module `Mathlib.AlgebraicTopology.ModelCategory.Cylinder` | package Mathlib | The precylinder object obtained by switching the two inclusions.

### Query: `OnReflectingArc`
- `ContinuousOn` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A function between topological spaces is continuous on a subset `s` when it's continuous at every point of `s` within `s`.
- `Circle.centeredArc` | module `Mathlib.Analysis.SpecialFunctions.Complex.Circle` | package Mathlib | The image under `Circle.exp` of the interval of angles `(-r, r)`.
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...

### Query: `GeometricRay`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Function.Injective.sameRay_map_iff` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The images of two vectors under an injective linear map are on the same ray if and only if the original vectors are on the same ray.

### Query: `ParallelIncidentRayFamily`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `AffineSubspace.instReflParallel` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` | package Mathlib | **Reflexivity of Parallelism for Affine Subspaces.** The parallelism relation on affine subspaces is reflexive; that is, every affine subspace is parallel to itself.
- `CategoryTheory.Limits.parallelFamily` | module `Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers` | package Mathlib | `parallelFamily f` is the diagram in `C` consisting of the given family of morphisms, each with common domain and codomain.

### Query: `AlignedWithMirror`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `LipschitzWith` | module `Mathlib.Topology.EMetricSpace.Lipschitz` | package Mathlib | A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, y` we have `dist (f x) (f y) ≤ K * dist x y`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `ReflectionEvent`
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `IsSpecularReflection`
- `CoxeterSystem.IsReflection` | module `Mathlib.GroupTheory.Coxeter.Inversion` | package Mathlib | `t : W` is a *reflection* of the Coxeter system `cs` if it is of the form $w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `LinearMap.IsReflective` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is injective, and for any vector `y`, the norm of `x` divides twice the inner product of `x` and `y`. These conditions are what...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `crossProduct` (Mathlib)
- `Projectivization.cross` (Mathlib)
- `cross_cross` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `HomotopicalAlgebra.Precylinder.symm` (Mathlib)
- `ContinuousOn` (Mathlib)
- `Circle.centeredArc` (Mathlib)
- `Module.reflection` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Function.Injective.sameRay_map_iff` (Mathlib)
- `SameRay` (Mathlib)
- `AffineSubspace.instReflParallel` (Mathlib)
- `CategoryTheory.Limits.parallelFamily` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `LipschitzWith` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Module.reflection` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `CoxeterSystem.IsReflection` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `LinearMap.IsReflective` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_2_A_1.AlignedWithMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.CrossSectionPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.Figure2cTo2eLimitingGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.GeometricRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.HalfCylindricalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.IsReflectionThreshold`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.IsSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.MirrorDynamics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.OnReflectingArc`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.ParallelIncidentRayFamily`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.ReflectionEvent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_A_1.ReflectionTrace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
