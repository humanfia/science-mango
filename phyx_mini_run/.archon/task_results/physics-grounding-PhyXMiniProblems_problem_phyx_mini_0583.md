# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0583.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0583.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2664ecd633d465ce6f6836d0b3f17b62b1e86ca159f514706c88d8ce8cfb381d
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Signed Length Quantity`
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `signed Length Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist_neg` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Negation of the Reference Vector in Signed Distance.** The signed distance from a point $p$ to a point $q$ with respect to the negation of a reference vector $v$ is equal to the negative of the signed distance from...

### Query: `length In Picometers`
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `signed Length In Picometers`
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Quantum Particle Kind`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `ClassicalMechanics.FreeParticle.Trajectory` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A trajectory is a time-dependent position function describing the motion of the particle in one spatial dimension. Defining the trajectory.
- `ClassicalMechanics.FreeParticle.velocity` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | The velocity of a trajectory at a given time. This is defined as the time derivative of the position function.

### Query: `Corral Confinement`
- `CategoryTheory.Limits.Cofork` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | A cofork on `f` and `g` is just a `Cocone (parallelPair f g)`.
- `CategoryTheory.Limits.IsColimit` | module `Mathlib.CategoryTheory.Limits.IsLimit` | package Mathlib | A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique cocone morphism from `t`.
- `Matroid.restrict_isColoop_iff` | module `Mathlib.Combinatorics.Matroid.Loop` | package Mathlib | **Coloops of a Matroid Restriction.** Given a matroid $M$ and a subset $R$ of its ground set, an element $e$ is a coloop of the restriction $M|_R$ if and only if $e$ is in $R$ and $e$ does not belong to the closure of...

### Query: `Cartesian Axis Label`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `CategoryTheory.CartesianMonoidalCategory` | module `Mathlib.CategoryTheory.Monoidal.Cartesian.Basic` | package Mathlib | An instance of `CartesianMonoidalCategory C` bundles an explicit choice of a binary product of two objects of `C`, and a terminal object in `C`. Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_...
- `CategoryTheory.CartesianMonoidalCategory.lift` | module `Mathlib.CategoryTheory.Monoidal.Cartesian.Basic` | package Mathlib | Constructs a morphism to the product given its two components.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `signedDist` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist_neg` (Mathlib)
- `LengthUnit.picometers` (PhysLean)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `ClassicalMechanics.FreeParticle.Trajectory` (PhysLean)
- `ClassicalMechanics.FreeParticle.velocity` (PhysLean)
- `CategoryTheory.Limits.Cofork` (Mathlib)
- `CategoryTheory.Limits.IsColimit` (Mathlib)
- `Matroid.restrict_isColoop_iff` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `CategoryTheory.CartesianMonoidalCategory` (Mathlib)
- `CategoryTheory.CartesianMonoidalCategory.lift` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0583.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.CartesianAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.CorralConfinement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.FigureShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.InfiniteSquareCorralMode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.MatchesProblemStatementAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.QuantumParticleKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.RoundsToNearestTenThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.SatisfiesInfiniteSquareCorralPhysics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.SignedLengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.SquareCorralExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.SquareCorralFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0583.SquarePositionProbe`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
