# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0063.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0063.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1494db04555e0952868eba7dc453ae0b4e62ff50757d64c1e3b9598eca1c7fe2
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

### Query: `meters Value`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.

### Query: `Point2 D`
- `TwoPointing.pi_snd` | module `Mathlib.Data.TwoPointing` | package Mathlib | **Second component of a product two-pointing.** The second distinguished element of the two-pointing on the function space $\alpha \to \beta$ (induced by a two-pointing $q$ on $\beta$) is the constant function that ma...
- `prevD` | module `Mathlib.Algebra.Homology.Homotopy` | package Mathlib | The composition `f j (c.prev j) ≫ D.d (c.prev j) j`.
- `TwoPointing.prod` | module `Mathlib.Data.TwoPointing` | package Mathlib | The product of two two-pointings.

### Query: `x Meters`
- `Polynomial.X` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `X` is the polynomial variable (aka indeterminate).
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `y Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `Rectangular Room`
- `Orientation.areaForm` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual notation `ω`). When evaluated on two vectors, it gives the oriented area of the parallelogram they span.
- `Orientation.rightAngleRotation` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation `J`). This automorphism squares to -1. We will define rotations in such a way that this automorphism is equal to rotatio...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.

### Query: `width Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Subgroup.widthInfty` | module `Mathlib.NumberTheory.ModularForms.Cusps` | package Mathlib | The width of the cusp `∞`, i.e. the `x` such that `𝒢.periods = zmultiples x`, or 0 if no such `x` exists.
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `height Meters`
- `Ideal.height` | module `Mathlib.RingTheory.Ideal.Height` | package Mathlib | The height of an ideal is defined as the infimum of the heights of its minimal prime ideals.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Rat.mulHeight₁_natCast` | module `Mathlib.NumberTheory.Height.NumberField` | package Mathlib | The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n`.

### Query: `Room Boundary`
- `Topology.RelCWComplex.cellFrontier` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | The boundary of the `n`-cell given by the index `i`. Use this instead of `map n i '' sphere 0 1` whenever possible.
- `Cube.boundary` | module `Mathlib.Topology.Homotopy.HomotopyGroup` | package Mathlib | The points in a cube with at least one projection equal to 0 or 1.
- `Coheyting.boundary` | module `Mathlib.Order.Heyting.Boundary` | package Mathlib | The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with itself. Note that this is always `⊥` for a Boolean algebra.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `TwoPointing.pi_snd` (Mathlib)
- `prevD` (Mathlib)
- `TwoPointing.prod` (Mathlib)
- `Polynomial.X` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `Orientation.areaForm` (Mathlib)
- `Orientation.rightAngleRotation` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Subgroup.widthInfty` (Mathlib)
- `LengthUnit.miles` (PhysLean)
- `Ideal.height` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Rat.mulHeight₁_natCast` (Mathlib)
- `Topology.RelCWComplex.cellFrontier` (Mathlib)
- `Cube.boundary` (Mathlib)
- `Coheyting.boundary` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0063.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.CeilingMirrorLaserSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.HasAcuteLaunchAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.HasPhysicalPathGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.IsBottomLeftCorner`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.IsMidpointOfFarWall`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.LaunchAngleDescribesIncidentRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.LiesOnBoundary`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.MatchesAnswerToNearestDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.ObeysSpecularReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.Point2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.RectangularRoom`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0063.RoomBoundary`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
