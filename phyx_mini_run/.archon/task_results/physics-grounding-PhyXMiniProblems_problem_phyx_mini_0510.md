# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0510.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0510.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:781c9d09f77d2d2744b9a8f76273c2ce7459464163b6c2c612401f3a6456fdc5
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Velocity Quantity`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.velocity_eq` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | **Velocity of a Material Point.** For a rigid body motion $M$ in $d$-dimensional space, the velocity of a material point $y$ at time $t$ is equal to the time derivative of the displacement of $y$ evaluated at $t$.

### Query: `velocity Readout`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | The trajectory resulting from `toInitialConditions` has the specified velocity `v_t₀` at time `t₀`.

### Query: `vacuum Speed Of Light Readout`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `velocity In Light Speed Units`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Reference Frame Label`
- `Bundle.Trivialization.localFrame_coeff` | module `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame` | package Mathlib | Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`. If x is outside of `e.baseSet`, this returns the junk value 0.
- `FrameHom` | module `Mathlib.Order.Hom.CompleteLattice` | package Mathlib | The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
- `Order.Frame` | module `Mathlib.Order.CompleteBooleanAlgebra` | package Mathlib | A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`.

### Query: `Axis Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Figure Object Label`
- `CategoryTheory.ObjectProperty` | module `Mathlib.CategoryTheory.ObjectProperty.Basic` | package Mathlib | A property of objects in a category `C` is a predicate `C → Prop`.
- `Quiver.SchreierGraph.labelling_obj` | module `Mathlib.Combinatorics.Quiver.Schreier` | package Mathlib | **Schreier Graph Labeling Prefunctor on Objects.** The object component of the labeling prefunctor from a Schreier graph to the single-object quiver of a set $S$ maps every vertex of the Schreier graph to the unique o...
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.

### Query: `Axial Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.velocity_eq` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` (PhysLean)
- `LightProfinite` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `DimSpeed.speedOfLight` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `LightProfinite` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `Bundle.Trivialization.localFrame_coeff` (Mathlib)
- `FrameHom` (Mathlib)
- `Order.Frame` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `CategoryTheory.ObjectProperty` (Mathlib)
- `Quiver.SchreierGraph.labelling_obj` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Space.toDirection` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0510.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.AxialDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.AxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.FigureObjectLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.MatchesAuxiliaryScoutshipReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.MatchesFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.ObeysCollinearRelativisticVelocityAddition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.ReferenceFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.RelativisticProbeSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.RoundsToNearestThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0510.VelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
