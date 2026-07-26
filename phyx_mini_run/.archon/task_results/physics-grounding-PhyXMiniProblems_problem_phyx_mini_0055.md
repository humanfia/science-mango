# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0055.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0055.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d7f75a860c8ef025dbafc6b0af44385ffc20d2c05f25aa50f2d4f07ead0e847f
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `Polynomial.derivative` | module `Mathlib.Algebra.Polynomial.Derivative` | package Mathlib | `derivative p` is the formal derivative of the polynomial `p`
- `bernsteinPolynomial.iterate_derivative_at_1` | module `Mathlib.RingTheory.Polynomial.Bernstein` | package Mathlib | **The $(n-\nu)$-th Derivative of a Bernstein Polynomial at 1.** For a commutative ring $R$ and natural numbers $\nu \leq n$, the $(n-\nu)$-th iterative derivative of the Bernstein polynomial $B_{\nu, n}(X)$ evaluated...
- `derivWithin_zero_of_not_accPt` | module `Mathlib.Analysis.Calculus.Deriv.Basic` | package Mathlib | **Derivative at an Isolated Point.** If a point $x$ is not an accumulation point of a set $s$, then the derivative of any function $f$ within $s$ at $x$ is zero.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `Fish Bowl Refraction Setup`
- `fish_pure` | module `Mathlib.Control.Basic` | package Mathlib | **Right Identity of Kleisli Composition.** For any function $f$ from a type $\alpha$ to a monadic type $m \beta$, the Kleisli composition of $f$ with the monadic `pure` operation is equal to $f$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `EuclideanGeometry.oangle_pointReflection_left` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | **Oriented Angle under Point Reflection of the First Point.** For any three points $p_1, p_2, p_3$ in a Euclidean geometry such that $p_1 \neq p_2$ and $p_3 \neq p_2$, the oriented angle $\sphericalangle (p_1' p_2 p_3...

### Query: `Meridional Ray Family`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

### Query: `answer Distance In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `Metric.infEDist` | module `Mathlib.Topology.MetricSpace.HausdorffDistance` | package Mathlib | The minimal edistance of a point to a set
- `EuclideanGeometry.dist_inversion_center` | module `Mathlib.Geometry.Euclidean.Inversion.Basic` | package Mathlib | Distance from the image of a point under inversion to the center. This formula accidentally works for `x = c`.

### Query: `problem phyx mini 0055`
- `Minimal` | module `Mathlib.Order.Defs.Unbundled` | package Mathlib | `Minimal P x` means that `x` is a minimal element satisfying `P`.
- `MinimalFor.prop` | module `Mathlib.Order.Defs.Unbundled` | package Mathlib | **Minimal Element Property.** If an index $i$ is minimal for a function $f$ with respect to a property $P$, then $i$ satisfies the property $P$.
- `maximal_iff_forall_gt` | module `Mathlib.Order.Minimal` | package Mathlib | **Characterization of Minimal Elements.** An element $x$ satisfies the property $P$ and is minimal with respect to $P$ if and only if $P(x)$ holds and there is no element $y < x$ such that $P(y)$ holds.

## Grounded Mathlib/PhysLean names

- `Polynomial.derivative` (Mathlib)
- `bernsteinPolynomial.iterate_derivative_at_1` (Mathlib)
- `derivWithin_zero_of_not_accPt` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `fish_pure` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `EuclideanGeometry.oangle_pointReflection_left` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `RayVector` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `Metric.infEDist` (Mathlib)
- `EuclideanGeometry.dist_inversion_center` (Mathlib)
- `Minimal` (Mathlib)
- `MinimalFor.prop` (Mathlib)
- `maximal_iff_forall_gt` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0055.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0055.FishBowlRefractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0055.MeridionalRayFamily`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0055.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
