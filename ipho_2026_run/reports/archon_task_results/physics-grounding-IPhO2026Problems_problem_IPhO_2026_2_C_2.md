# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:713366da9ff5ffd542074414dc3a24cbfd2155dd22b958ab89fac9342ef46e62
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `Polynomial.derivative` | module `Mathlib.Algebra.Polynomial.Derivative` | package Mathlib | `derivative p` is the formal derivative of the polynomial `p`
- `bernsteinPolynomial.iterate_derivative_at_1` | module `Mathlib.RingTheory.Polynomial.Bernstein` | package Mathlib | **The $(n-\nu)$-th Derivative of a Bernstein Polynomial at 1.** For a commutative ring $R$ and natural numbers $\nu \leq n$, the $(n-\nu)$-th iterative derivative of the Bernstein polynomial $B_{\nu, n}(X)$ evaluated...
- `derivWithin_zero_of_not_accPt` | module `Mathlib.Analysis.Calculus.Deriv.Basic` | package Mathlib | **Derivative at an Isolated Point.** If a point $x$ is not an accumulation point of a set $s$, then the derivative of any function $f$ within $s$ at $x$ is zero.

### Query: `ReflectedRayReadout`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.

### Query: `ReflectedRayReadout.yCoordinateLengthReadout`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_Y` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` | package Mathlib | **Multiplication by $Y$ in the Coordinate Ring of a Weierstrass Curve.** In the coordinate ring of an affine Weierstrass curve $W'$ over a commutative ring $R$, let $X$ and $Y$ denote the standard generators. For any...
- `CoxeterSystem.IsReflection.odd_length` | module `Mathlib.GroupTheory.Coxeter.Inversion` | package Mathlib | **Parity of Reflection Length.** In a Coxeter system, the length of any reflection is an odd number.

### Query: `Figure2gSetup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Function.Pullback.snd` | module `Mathlib.Data.Set.Prod` | package Mathlib | The projection from the fiber product to the second factor.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.

### Query: `rayA`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.

### Query: `rayB`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `Module.Ray.someVector_ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | The ray of `someVector`.

### Query: `HalfCylindricalReflectionLaw`
- `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right` | module `Mathlib.Geometry.Euclidean.Sphere.Basic` | package Mathlib | **Point Reflection of a Diameter Endpoint.** If two points $p_1$ and $p_2$ form a diameter of a sphere $s$, then the reflection of $p_2$ across the center of $s$ is equal to $p_1$.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `parallelogram_law` | module `Mathlib.Analysis.InnerProductSpace.Basic` | package Mathlib | Parallelogram law

### Query: `PreviousPartC1Result`
- `Part` | module `Mathlib.Data.Part` | package Mathlib | `Part α` is the type of "partial values" of type `α`. It is similar to `Option α` except the domain condition can be an arbitrary proposition, not necessarily decidable.
- `ComplexShape.prev_eq'` | module `Mathlib.Algebra.Homology.ComplexShape` | package Mathlib | **Previous Index of a Related Pair.** For a complex shape $c$ and indices $i, j$, if $i$ is related to $j$ in $c$, then the previous index of $j$ is equal to $i$.
- `Mathlib.Command.MinImports.previousInstName` | module `Mathlib.Tactic.MinImports` | package Mathlib | `previousInstName nm` takes as input a name `nm`, assuming that it is the name of an auto-generated "nameless" `instance`. If `nm` ends in `..._n`, where `n` is a number, it returns the same name, but with `_n` replac...

### Query: `rayB slope firstOrder`
- `slope` | module `Mathlib.LinearAlgebra.AffineSpace.Slope` | package Mathlib | `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval `[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`.
- `slope_pos_iff` | module `Mathlib.LinearAlgebra.AffineSpace.Ordered` | package Mathlib | **Positivity of the Slope.** Let $f$ be a function on a strictly ordered field. For any two points $x_0$ and $b$ such that $x_0 < b$, the slope of $f$ between $x_0$ and $b$ is positive if and only if $f(x_0) < f(b)$.
- `slope_pos_iff_gt` | module `Mathlib.LinearAlgebra.AffineSpace.Ordered` | package Mathlib | **Positivity of the Slope.** In a strictly ordered field, given a function $f$ and two points $x_0$ and $b$ such that $b < x_0$, the slope of $f$ between $x_0$ and $b$ is positive if and only if $f(b) < f(x_0)$.

### Query: `rayB intercept firstOrder`
- `FirstOrder.«term_≅[_]_»` | module `Mathlib.ModelTheory.Semantics` | package Mathlib | Two structures are elementarily equivalent when they satisfy the same sentences.
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `Set.Ioc_inter_Ioi` | module `Mathlib.Order.Interval.Set.LinearOrder` | package Mathlib | **Intersection of a Left-Open Right-Closed Interval and an Open Upper Ray.** For any elements $a, b,$ and $c$ in a linear order, the intersection of the left-open right-closed interval $(a, b]$ and the open upper ray...

## Grounded Mathlib/PhysLean names

- `Polynomial.derivative` (Mathlib)
- `bernsteinPolynomial.iterate_derivative_at_1` (Mathlib)
- `derivWithin_zero_of_not_accPt` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `SameRay` (Mathlib)
- `WeierstrassCurve.Affine.CoordinateRing.smul_basis_mul_Y` (Mathlib)
- `CoxeterSystem.IsReflection.odd_length` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Function.Pullback.snd` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `RayVector` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `Module.Ray.someVector_ray` (Mathlib)
- `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `parallelogram_law` (Mathlib)
- `Part` (Mathlib)
- `ComplexShape.prev_eq'` (Mathlib)
- `Mathlib.Command.MinImports.previousInstName` (Mathlib)
- `slope` (Mathlib)
- `slope_pos_iff` (Mathlib)
- `slope_pos_iff_gt` (Mathlib)
- `FirstOrder.«term_≅[_]_»` (Mathlib)
- `Set.Ioi` (Mathlib)
- `Set.Ioc_inter_Ioi` (Mathlib)

## Local abstractions introduced

- `IPhO2026_2_C_2.Figure2gSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_2_C_2.HalfCylindricalReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_2_C_2.IPhO_2026_2_C_2`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_2_C_2.PreviousPartC1Result`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_2_C_2.ReflectedRayReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
