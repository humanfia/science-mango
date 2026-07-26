# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0028.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0028.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:bb4d38422603f00104283138caed47386f99ef86c638aac12fc1a48d80319410
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length Value`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `centimeter Value`
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `TimeUnit.centiseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of centiseconds (10⁻² of a second).

### Query: `Plano Convex Lens`
- `Convex` | module `Mathlib.Analysis.Convex.Basic` | package Mathlib | Convexity of sets.
- `Complex.starConvex_slitPlane` | module `Mathlib.Analysis.Complex.Convex` | package Mathlib | The slit plane is star-convex at a positive number.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Is Physical Plano Convex Lens`
- `Convex` | module `Mathlib.Analysis.Convex.Basic` | package Mathlib | Convexity of sets.
- `Complex.starConvex_slitPlane` | module `Mathlib.Analysis.Complex.Convex` | package Mathlib | The slit plane is star-convex at a positive number.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Parallel Axis Ray Trace`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | **Same Ray Condition in Two Dimensions.** For any two vectors $x$ and $y$ in an oriented two-dimensional inner product space, $x$ and $y$ lie on the same ray if and only if their inner product is non-negative and the...

### Query: `Snell Law At Interface`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Law of sines** (sine rule), vector angle form.
- `EuclideanGeometry.law_sin` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Alias** of `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. --- **Law of sines** (sine rule), angle-at-point form.

### Query: `Satisfies Spherical Exit Ray Law`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_of_radius_lt_dist` | module `Mathlib.Geometry.Euclidean.Sphere.OrthRadius` | package Mathlib | **Empty Intersection of a Sphere and its Orthogonal Radius.** If a point $p$ lies outside a sphere $s$ (that is, the distance from $p$ to the center of $s$ is strictly greater than the radius of $s$), then the interse...
- `EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_iff` | module `Mathlib.Geometry.Euclidean.Sphere.OrthRadius` | package Mathlib | **Intersection of a Sphere and an Orthogonal Radius.** The intersection of a sphere $s$ and the line passing through a point $p$ and the sphere's center (the orthogonal radius at $p$) is empty if and only if one of th...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `Computation.length` (Mathlib)
- `Computation.length_pure` (Mathlib)
- `LengthUnit` (PhysLean)
- `spectralValue` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `TimeUnit.centiseconds` (PhysLean)
- `Convex` (Mathlib)
- `Complex.starConvex_slitPlane` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `Convex` (Mathlib)
- `Complex.starConvex_slitPlane` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `SameRay` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` (Mathlib)
- `EuclideanGeometry.law_sin` (Mathlib)
- `SameRay` (Mathlib)
- `EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_of_radius_lt_dist` (Mathlib)
- `EuclideanGeometry.Sphere.inter_orthRadius_eq_empty_iff` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0028.IsPhysicalPlanoConvexLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0028.ParallelAxisRayTrace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0028.PlanoConvexLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0028.SatisfiesSphericalExitRayLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0028.SnellLawAtInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
