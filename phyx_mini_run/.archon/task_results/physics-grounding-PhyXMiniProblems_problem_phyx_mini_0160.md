# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0160.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0160.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:46fbfe2b40166dba0e95b633a8215c7b23496069e822de848ca0bd619780a8d8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Spherical Mirror Kind`
- `Cosmology.SpatialGeometry.Spherical` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | **Spherical Spatial Geometry.** A spherical spatial geometry is characterized by a curvature parameter $k$ that is strictly less than zero.
- `Metric.sphere` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `sphere x ε` is the set of all points `y` with `dist y x = ε`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Graph Variable`
- `Mathlib.Command.Variable.variable?` | module `Mathlib.Tactic.Variable` | package Mathlib | The `variable?` command has the same syntax as `variable`, but it will auto-insert missing instance arguments wherever they are needed. It does not add variables that can already be deduced from others in the current...
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `WeierstrassCurve.VariableChange` | module `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange` | package Mathlib | An admissible linear change of variables of Weierstrass curves defined over a ring `R` given by a tuple `(u, r, s, t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. As a matrix, it is $$\begin{pmatrix} u^2 & 0 & r \...

### Query: `Spherical Mirror Magnification Setup`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.
- `Metric.sphere` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `sphere x ε` is the set of all points `y` with `dist y x = ε`
- `EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_left` | module `Mathlib.Geometry.Euclidean.Sphere.Basic` | package Mathlib | **Characterization of a Sphere's Diameter via Point Reflection.** Two points $p_1$ and $p_2$ form a diameter of a sphere $s$ if and only if $p_1$ lies on the sphere and $p_2$ is the image of $p_1$ under a point reflec...

### Query: `Matches Problem And Graph`
- `SimpleGraph.ConnectedComponent.odd_matches_node_outside` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Perfect Matchings and Odd Components.** In a finite graph with a perfect matching $M$, for any set of vertices $U$, every odd connected component of the subgraph induced by the remaining vertices $V \setminus U$ mus...
- `SimpleGraph.Subgraph.IsMatching.coeSubgraph` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Matching Property of Nested Subgraphs.** Let $G'$ be a subgraph of a simple graph $G$. If $M$ is a subgraph of $G'$ (viewed as a standalone graph) and $M$ is a matching, then the corresponding subgraph of $G$ induce...
- `SimpleGraph.Subgraph.IsPerfectMatching.isAlternating_symmDiff_right` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Alternating Property of the Symmetric Difference of Perfect Matchings.** Let $M$ and $M'$ be perfect matchings of a simple graph $G$. Then the symmetric difference of $M$ and $M'$ is an alternating graph with respec...

### Query: `Has Figure Derived Focal Calibration`
- `HasDerivedCategory` | module `Mathlib.Algebra.Homology.DerivedCategory.Basic` | package Mathlib | The assumption that a localized category for `(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that the morphisms in this chosen category are in `Type w`.
- `DerivedCategory.Q` | module `Mathlib.Algebra.Homology.DerivedCategory.Basic` | package Mathlib | The localization functor `CochainComplex C ℤ ⥤ DerivedCategory C`.
- `Subgroup.focalSubgroup` | module `Mathlib.GroupTheory.Focal` | package Mathlib | The **Focal Subgroup** of a subgroup `H` (denoted `H*` or `foc(H)`). It is generated by elements of the form `x⁻¹ * (u * x * u⁻¹)` where both `x` and `x^u` are in `H`.

### Query: `Has Physical Parameters`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Cosmology.SpatialGeometry.Spherical` (PhysLean)
- `Metric.sphere` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Mathlib.Command.Variable.variable?` (Mathlib)
- `SimpleGraph` (Mathlib)
- `WeierstrassCurve.VariableChange` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `Metric.sphere` (Mathlib)
- `EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_left` (Mathlib)
- `SimpleGraph.ConnectedComponent.odd_matches_node_outside` (Mathlib)
- `SimpleGraph.Subgraph.IsMatching.coeSubgraph` (Mathlib)
- `SimpleGraph.Subgraph.IsPerfectMatching.isAlternating_symmDiff_right` (Mathlib)
- `HasDerivedCategory` (Mathlib)
- `DerivedCategory.Q` (Mathlib)
- `Subgroup.focalSubgroup` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `Dimension` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0160.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.GraphVariable`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.HasFigureDerivedFocalCalibration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.IsFiniteObjectConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.MatchesDisplayedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.MatchesProblemAndGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.SatisfiesParaxialSphericalMirrorLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.SphericalMirrorKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0160.SphericalMirrorMagnificationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
