# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0053.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0053.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1cc1369abba1fb95b9163f9fb2ec9ff7ae5238daac68313bc10545439f504020
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

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Thin Lens Kind`
- `CategoryTheory.ThinSkeleton` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | Construct the skeleton category by taking the quotient of objects. This construction gives a preorder with nice definitional properties, but is only really appropriate for thin categories. If your original category is...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.ThinSkeleton.thin` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | The thin skeleton is thin.

### Query: `Geometrical Image Kind`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `Cosmology.SpatialGeometry` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)`
- `AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral` | module `Mathlib.AlgebraicGeometry.Geometrically.Integral` | package Mathlib | **Geometrically Integral implies Geometrically Reduced.** Every geometrically integral morphism of schemes is also a geometrically reduced morphism.

### Query: `Image Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Orientation.rotation_rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | Rotating twice is equivalent to rotating by the sum of the angles.

### Query: `Principal Axis Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.principal_axes_of_inertia` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Because the inertia tensor is real symmetric, there exists an orthonormal basis of principal axes in which it is diagonal. The corresponding directions are the principal axes of inertia.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Figure Ray Label`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Module.Ray.map_refl` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | **Identity Map of Module Rays.** The map induced on the set of rays of a module $M$ by the identity linear equivalence on $M$ is the identity equivalence on the set of rays.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `CategoryTheory.ThinSkeleton` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.thin` (Mathlib)
- `Set.image` (Mathlib)
- `Cosmology.SpatialGeometry` (PhysLean)
- `AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Orientation.rotation_rotation` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.principal_axes_of_inertia` (PhysLean)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Module.Ray.map_refl` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0053.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.DivergingLensSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.FigureRayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.GeometricalImageKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.HasPhysicalSignConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.ImageOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.IsNearestHundredthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.ObeysSignedThinLensEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.ObeysTransverseMagnificationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.PrincipalAxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.ThinLensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0053.UsesCartesianSignConvention`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
