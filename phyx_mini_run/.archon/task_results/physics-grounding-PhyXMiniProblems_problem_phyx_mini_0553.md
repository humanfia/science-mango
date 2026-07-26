# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0553.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0553.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:88e64947d406acd24c42fe64124ef7753925c3e437a1e2165fa06605218d4520
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `vacuum Speed Of Light Readout`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `speed Fraction Of Vacuum Light`
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `Int.fract` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.fract a` the fractional part of `a`, is `a` minus its floor.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Inertial Frame Label`
- `RigidBody.translational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the translational equation of motion of a rigid body is given by dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting on the body.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `RigidBody.rotational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the rotational equation of motion of a rigid body about the center of mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total external torque.

### Query: `Frame Origin Label`
- `Bundle.Trivialization.localFrame_coeff` | module `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame` | package Mathlib | Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`. If x is outside of `e.baseSet`, this returns the junk value 0.
- `FrameHom` | module `Mathlib.Order.Hom.CompleteLattice` | package Mathlib | The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
- `Frame.copy` | module `Mathlib.Order.Copy` | package Mathlib | A function to create a provable equal copy of a frame with possibly different definitional equalities.

### Query: `origin Frame`
- `Bundle.Trivialization.localFrame_coeff` | module `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame` | package Mathlib | Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`. If x is outside of `e.baseSet`, this returns the junk value 0.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `Order.Frame` | module `Mathlib.Order.CompleteBooleanAlgebra` | package Mathlib | A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`.

### Query: `Horizontal Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `Figure Velocity Arrow`
- `Lorentz.Velocity.pathFromZero` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A continuous path from a velocity `u` to the zero velocity.
- `CategoryTheory.Arrow` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative squares in `T`.
- `CategoryTheory.Arrow.Hom.left` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The left part of a morphism in the category of arrows.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `LightProfinite` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `DimSpeed.speedOfLight` (PhysLean)
- `SpeedOfLight` (PhysLean)
- `Int.fract` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `RigidBody.translational_equation_inertial` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `RigidBody.rotational_equation_inertial` (PhysLean)
- `Bundle.Trivialization.localFrame_coeff` (Mathlib)
- `FrameHom` (Mathlib)
- `Frame.copy` (Mathlib)
- `Bundle.Trivialization.localFrame_coeff` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Order.Frame` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Turing.Dir.left` (Mathlib)
- `Lorentz.Velocity.pathFromZero` (PhysLean)
- `CategoryTheory.Arrow` (Mathlib)
- `CategoryTheory.Arrow.Hom.left` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0553.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.EarthSpaceshipMissileFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.EarthSpaceshipMissileSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.FigureVelocityArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.FrameOriginLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.HasPhysicalSpeedParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.IsUniqueMatchingAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.RoundsToNearestHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.SatisfiesCollinearEinsteinVelocityAddition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0553.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
