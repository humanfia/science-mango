# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0590.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0590.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8901ff70f2daf33106d70c1297d07434292a4954ffac7f2c46687108106ff88e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Signed Velocity Quantity`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.

### Query: `signed Velocity Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | The trajectory resulting from `toInitialConditions` has the specified velocity `v_t₀` at time `t₀`.

### Query: `signed Velocity In Meters Per Second`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `vacuum Light Speed In Meters Per Second`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `Electromagnetism.EMSystem.c` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The speed of light.

### Query: `velocity Fraction Of Light`
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.

### Query: `Ship Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Quiver.Labelling` | module `Mathlib.Combinatorics.Quiver.Subquiver` | package Mathlib | An `L`-labelling of a quiver assigns to every arrow an element of `L`.

### Query: `Inertial Frame Label`
- `RigidBody.translational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the translational equation of motion of a rigid body is given by dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting on the body.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `RigidBody.rotational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the rotational equation of motion of a rigid body about the center of mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total external torque.

### Query: `Horizontal Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `Figure Color`
- `SimpleGraph.Colorable` | module `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex` | package Mathlib | Whether a graph can be colored by at most `n` colors.
- `Besicovitch.TauPackage.color` | module `Mathlib.MeasureTheory.Covering.Besicovitch` | package Mathlib | Group the balls into disjoint families, by assigning to a ball the smallest color for which it does not intersect any already chosen ball of this color.
- `Combinatorics.Line.ColorFocused` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | The type of collections of lines such that - each line is only one color except possibly at its endpoint - the lines all have the same endpoint - the colors of the lines are distinct. Used in the proof `exists_mono_in...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `signedDist` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `signedDist` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` (PhysLean)
- `signedDist` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `Electromagnetism.EMSystem.c` (PhysLean)
- `SpeedOfLight` (PhysLean)
- `LightProfinite` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Quiver.Labelling` (Mathlib)
- `RigidBody.translational_equation_inertial` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `RigidBody.rotational_equation_inertial` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Turing.Dir.left` (Mathlib)
- `SimpleGraph.Colorable` (Mathlib)
- `Besicovitch.TauPackage.color` (Mathlib)
- `Combinatorics.Line.ColorFocused` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0590.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.ApproachesShipBWithEqualSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.FigureAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.FigureColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.FigureVelocityLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.HasPhysicalVelocityParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.IsUniqueMatchingAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.RoundsToNearestThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.SatisfiesCollinearEinsteinVelocityTransformation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.ShipLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.SignedVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.ThreeSpaceshipChaseFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0590.ThreeSpaceshipChaseSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
