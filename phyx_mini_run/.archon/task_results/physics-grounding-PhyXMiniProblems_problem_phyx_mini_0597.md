# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0597.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0597.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c7c44144fa96d94af099f61f2ae9d1b2fd81cd8067405bd9bd093a102597cc12
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Inertial Frame Label`
- `RigidBody.translational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the translational equation of motion of a rigid body is given by dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting on the body.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `RigidBody.rotational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the rotational equation of motion of a rigid body about the center of mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total external torque.

### Query: `relative Speed In Meters Per Second`
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `longitudinal Velocity Fraction Of C`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `Polynomial.C` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `C a` is the constant polynomial `a`. `C` is provided as a ring homomorphism.
- `Lorentz.Velocity.norm_spatialPart_le_timeComponent` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | **Magnitude of the Spatial and Temporal Components of a Lorentz Velocity.** For any Lorentz velocity $v$, the Euclidean norm of its spatial part is less than or equal to the absolute value of its time component.

### Query: `Horizontal Axis Tick Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `Vertical Axis Label`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the vertical identity 2-square.

### Query: `Supplied Velocity Graph`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `Digraph.sup_adj` | module `Mathlib.Combinatorics.Digraph.Basic` | package Mathlib | **Adjacency in the Supremum of Directed Graphs.** For any two directed graphs $x$ and $y$ on a vertex set $V$, a vertex $v$ is adjacent to a vertex $w$ in the supremum $x \sqcup y$ if and only if $v$ is adjacent to $w...

### Query: `Relativistic Velocity Graph Setup`
- `Lorentz.Velocity.pathFromZero` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A continuous path from a velocity `u` to the zero velocity.
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.

### Query: `particle Longitudinal Velocity In Meters Per Second`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Matches Supplied Velocity Graph`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `SimpleGraph` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`. The relation describes which pairs of vertices are adjacent. There is exactly one edge for every pair of adjacent vertices; see `SimpleGr...
- `SimpleGraph.Subgraph.IsMatching.iSup` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Matching of a Union of Subgraphs.** Let $\{H_i\}_{i \in I}$ be a family of subgraphs of a graph $G$. If each $H_i$ is a matching and the supports of the subgraphs are pairwise disjoint, then the supremum (union) of...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `RigidBody.translational_equation_inertial` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `RigidBody.rotational_equation_inertial` (PhysLean)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `Polynomial.C` (Mathlib)
- `Lorentz.Velocity.norm_spatialPart_le_timeComponent` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `SimpleGraph` (Mathlib)
- `Digraph.sup_adj` (Mathlib)
- `Lorentz.Velocity.pathFromZero` (PhysLean)
- `SimpleGraph` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `SimpleGraph` (Mathlib)
- `SimpleGraph.Subgraph.IsMatching.iSup` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0597.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.HasPhysicalSpeedOfLight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.HorizontalAxisTickLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.MatchesSuppliedVelocityGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.RelativisticVelocityGraphSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.SatisfiesOneDimensionalLorentzVelocityLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.SuppliedVelocityGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0597.VerticalAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
