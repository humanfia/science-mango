# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0442.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0442.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c75197ba0dfdf0dd9f52445c54b7ae075b2ae4366d008b966a3f0155cbfbe7ad
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Gauss law divergence electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Space.distDiv_inv_pow_eq_dim` | module `Physlib.SpaceAndTime.Space.Norm.Basic` | package PhysLean | The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`) equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the Dirac delta at the origin....

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Spherical Mirror Kind`
- `Cosmology.SpatialGeometry.Spherical` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | **Spherical Spatial Geometry.** A spherical spatial geometry is characterized by a curvature parameter $k$ that is strictly less than zero.
- `Metric.sphere` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `sphere x ε` is the set of all points `y` with `dist y x = ε`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Principal Axis Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.principal_axes_of_inertia` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Because the inertia tensor is real symmetric, there exists an orthonormal basis of principal axes in which it is diagonal. The corresponding directions are the principal axes of inertia.

### Query: `Graph Axis`
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `aesop_graph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A variant of the `aesop` tactic for use in the graph library. Changes relative to standard `aesop`: - We use the `SimpleGraph` rule set in addition to the default rule sets. - We instruct Aesop's `intro` rule to unfol...
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `Distance Graph Quantity`
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `SimpleGraph.edist_boxProd` | module `Mathlib.Combinatorics.SimpleGraph.Prod` | package Mathlib | **Distance in the Cartesian Product of Graphs.** In the Cartesian product $G \square H$ of two simple graphs, the distance between any two vertices $(x_1, x_2)$ and $(y_1, y_2)$ is equal to the sum of the distance bet...
- `SimpleGraph.dist_bot` | module `Mathlib.Combinatorics.SimpleGraph.Metric` | package Mathlib | **Distance in the Empty Graph.** In the empty graph on a vertex set $V$ (the graph with no edges), the distance between any two vertices $u$ and $v$ is $0$.

### Query: `Mirror Distance Graph`
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `SimpleGraph.dist_bot` | module `Mathlib.Combinatorics.SimpleGraph.Metric` | package Mathlib | **Distance in the Empty Graph.** In the empty graph on a vertex set $V$ (the graph with no edges), the distance between any two vertices $u$ and $v$ is $0$.
- `SimpleGraph.dist_comm` | module `Mathlib.Combinatorics.SimpleGraph.Metric` | package Mathlib | **Symmetry of Distance in a Simple Graph.** For any two vertices $u$ and $v$ in a simple graph $G$, the distance from $u$ to $v$ is equal to the distance from $v$ to $u$.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Space.distDiv_inv_pow_eq_dim` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Cosmology.SpatialGeometry.Spherical` (PhysLean)
- `Metric.sphere` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.principal_axes_of_inertia` (PhysLean)
- `SimpleGraph` (Mathlib)
- `aesop_graph` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `SimpleGraph` (Mathlib)
- `SimpleGraph.edist_boxProd` (Mathlib)
- `SimpleGraph.dist_bot` (Mathlib)
- `SimpleGraph` (Mathlib)
- `SimpleGraph.dist_bot` (Mathlib)
- `SimpleGraph.dist_comm` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0442.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.DistanceGraphQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.GraphAsymptoteRepresentsFocalDistance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.GraphAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.HasPhysicalMirrorDistances`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.MatchesProblemAndIntendedGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.MirrorDistanceGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.PrincipalAxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.SatisfiesGaussianSphericalMirrorEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.SphericalMirrorExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0442.SphericalMirrorKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
