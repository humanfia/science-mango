# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0005.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0005.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `si Length Value`
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Container Geometry`
- `Cosmology.SpatialGeometry` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)`
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `AlgebraicGeometry.AlgebraicCycle` | module `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic` | package Mathlib | Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z` with locally finite support (see the module docstring for more details). Note: currently this is an abbrev to save som...

### Query: `Snell Law At Fluid Air Interface`
- `FluidDynamics.FluidState` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | The density and velocity fields of a fluid on `d`-dimensional space.
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Law of sines** (sine rule), vector angle form.

### Query: `Empty Container Far Edge Sightline`
- `SimpleGraph.DeleteFar.le_card_edgeFinset` | module `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` | package Mathlib | **Lower Bound on Edges for Graphs Far from the Empty Property.** If a graph $G$ is $r$-delete-far from a property $p$, and $p$ is satisfied by the empty graph (the graph with no edges), then the number of edges in $G$...
- `SimpleGraph.edgeSet` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | `G.edgeSet` is the edge set for `G`. This is an abbreviation for `edgeSetEmbedding G` that permits dot notation.
- `SimpleGraph.EdgeDisjointTriangles.farFromTriangleFree` | module `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic` | package Mathlib | **Edge-Disjoint Triangles and Triangle-Freeness.** If a simple graph $G$ on a vertex set of size $n$ contains a collection of edge-disjoint triangles such that the number of these triangles is at least $\epsilon n^2$,...

### Query: `Coin Center Visible At Same Viewing Angle`
- `IsVisible` | module `Mathlib.Analysis.Convex.Visible` | package Mathlib | Two points are visible to each other through a set if no point of that set lies strictly between them. By convention, a point `x` sees itself through any set `s`, even when `x ∈ s`.
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `CategoryTheory.Limits.BinaryBicone.toCocone_pt` | module `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` | package Mathlib | **Vertex of the Cocone Associated with a Binary Bicone.** For any binary bicone $c$ over objects $P$ and $Q$, the vertex of the cocone induced by $c$ is equal to the central object (or cone point) of the bicone $c$.

### Query: `refractive Index gt two makes coin Center invisible`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `LinearMap.IsReflective.of_dvd_two` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Vectors Dividing Two.** In a commutative ring with no zero divisors and where $2 \neq 0$, a vector $x$ is reflective with respect to a bilinear form $B$ if the scalar $B(x, x)$ divides $2$.
- `AffineEquiv.injective_pointReflection_left_of_module` | module `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv` | package Mathlib | **Injectivity of Point Reflection with Respect to the Center.** In an affine space over a ring $k$ where $2$ is invertible, the map that sends a center $x$ to the reflection of a fixed point $y$ across $x$ is injective.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UnitChoices.SI_length` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `Cosmology.SpatialGeometry` (PhysLean)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `AlgebraicGeometry.AlgebraicCycle` (Mathlib)
- `FluidDynamics.FluidState` (PhysLean)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` (Mathlib)
- `SimpleGraph.DeleteFar.le_card_edgeFinset` (Mathlib)
- `SimpleGraph.edgeSet` (Mathlib)
- `SimpleGraph.EdgeDisjointTriangles.farFromTriangleFree` (Mathlib)
- `IsVisible` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `CategoryTheory.Limits.BinaryBicone.toCocone_pt` (Mathlib)
- `Subgroup.index` (Mathlib)
- `LinearMap.IsReflective.of_dvd_two` (Mathlib)
- `AffineEquiv.injective_pointReflection_left_of_module` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0005.CoinCenterVisibleAtSameViewingAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0005.ContainerGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0005.EmptyContainerFarEdgeSightline`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0005.SnellLawAtFluidAirInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
