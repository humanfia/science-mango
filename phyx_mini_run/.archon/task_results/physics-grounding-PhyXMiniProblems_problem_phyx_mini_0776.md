# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0776.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0776.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `symmetry Axis Index`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `ComplexShape.symmetryEquiv_symm_apply_coe` | module `Mathlib.Algebra.Homology.ComplexShapeSigns` | package Mathlib | **Symmetry Equivalence of Total Complex Index Fibers.** For any index $j$ in the total complex index set $I_{12}$, the inverse of the symmetry equivalence maps an element in the fiber of the index mapping $\pi$ (assoc...
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `symmetry Axis Line`
- `AffineMap.lineMap` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `segment_symm` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Symmetry of the Line Segment.** For any two points $x$ and $y$ in a vector space, the line segment connecting $x$ to $y$ is equal to the line segment connecting $y$ to $x$.

### Query: `solid Right Circular Cone Region`
- `PointedCone.coe_ofConeComb` | module `Mathlib.Geometry.Convex.Cone.Pointed` | package Mathlib | **Pointed Cone from Conical Combinations.** For a nonempty set $C$ in a module $E$ over a semiring $R$, if $C$ is closed under conical combinations—meaning that for all $x, y \in C$ and all non-negative scalars $a, b...
- `CategoryTheory.Limits.Cone` | module `Mathlib.CategoryTheory.Limits.Cones` | package Mathlib | A `c : Cone F` is: * an object `c.pt` and * a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to `F`. Example: if `J` is a category coming from a poset then the data required to make a term of...
- `CircularPreorder` | module `Mathlib.Order.Circular` | package Mathlib | A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `sbtw` is transitive.

### Query: `moment Of Inertia About Symmetry Axis`
- `RigidBody.inertiaTensor_symmetric` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | **Symmetry of the Inertia Tensor.** For any rigid body in $d$-dimensional space, the inertia tensor is symmetric; that is, for all indices $i$ and $j$, the $(i, j)$-th component of the inertia tensor is equal to its $...
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `ProbabilityTheory.moment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment of a real random variable, `μ[X ^ p]`.

### Query: `Is Uniform Solid Right Circular Cone`
- `CircularPreorder` | module `Mathlib.Order.Circular` | package Mathlib | A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `sbtw` is transitive.
- `IsUniformEmbedding` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and injective. If `α` is a separated space, then the latter assumption follows from the former.
- `ConvexCone.toPointedCone_top` | module `Mathlib.Geometry.Convex.Cone.Pointed` | package Mathlib | **The Pointed Cone of the Universal Convex Cone.** The pointed cone associated with the universal (top) convex cone is itself the universal (top) pointed cone.

### Query: `uniform Solid Cone moment Of Inertia about symmetry Axis`
- `RigidBody.solidSphere_inertiaTensor` | module `Physlib.ClassicalMechanics.RigidBody.SolidSphere` | package PhysLean | The moment of inertia tensor of a solid sphere through its center of mass is `2/5 m R^2 * I`.
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `UniformSpace.ball_eq_of_symmetry` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | **Symmetry of Uniform Balls.** For any symmetric relation $V$ on a set, the ball centered at $x$ with respect to $V$ is equal to the set of all points $y$ such that $(y, x) \in V$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Subgroup.index` (Mathlib)
- `ComplexShape.symmetryEquiv_symm_apply_coe` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `AffineMap.lineMap` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `segment_symm` (Mathlib)
- `PointedCone.coe_ofConeComb` (Mathlib)
- `CategoryTheory.Limits.Cone` (Mathlib)
- `CircularPreorder` (Mathlib)
- `RigidBody.inertiaTensor_symmetric` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `ProbabilityTheory.moment` (Mathlib)
- `CircularPreorder` (Mathlib)
- `IsUniformEmbedding` (Mathlib)
- `ConvexCone.toPointedCone_top` (Mathlib)
- `RigidBody.solidSphere_inertiaTensor` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `UniformSpace.ball_eq_of_symmetry` (Mathlib)

## Local abstractions introduced

- `PhyXMini0776.IsUniformSolidRightCircularCone`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
