# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0523.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0523.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b62e975928cccd1fd7380da46f32155fb8e0b8c10874740b224d005142068521
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

### Query: `velocity Readout`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | The trajectory resulting from `toInitialConditions` has the specified velocity `v_t₀` at time `t₀`.

### Query: `velocity In Meters Per Second`
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Inertial Frame Label`
- `RigidBody.translational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the translational equation of motion of a rigid body is given by dP/dt = F, where `P` is the total linear momentum and `F` is the total external force acting on the body.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `RigidBody.rotational_equation_inertial` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | In the inertial frame, the rotational equation of motion of a rigid body about the center of mass is given by dM/dt = K, where `M` is the total angular momentum and `K` is the total external torque.

### Query: `Horizontal Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `Figure Velocity Arrow`
- `Lorentz.Velocity.pathFromZero` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A continuous path from a velocity `u` to the zero velocity.
- `CategoryTheory.Arrow` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative squares in `T`.
- `CategoryTheory.Arrow.Hom.left` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The left part of a morphism in the category of arrows.

### Query: `Printed Velocity Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `Lorentz.Velocity.zero` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | The `Velocity d` which has all space components zero.

### Query: `Figure Feature`
- `Partition.IsRepFun.apply_mem` | module `Mathlib.Order.Partition.Basic` | package Mathlib | **Membership of a Representative Function's Image.** If $f$ is a representative function for a partition $P$, then for any element $a$ belonging to a set $u$ in the partition, the image $f(a)$ also belongs to $u$.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Truck Baseball Figure`
- `Mathlib.Tactic.Widget.subTriangle` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Triangle with `homs = [f,g,h]` and `objs = [A,B,C]` ``` A f B h g C ```
- `CategoryTheory.Triangulated.TStructure.truncLT` | module `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE` | package Mathlib | Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this is the `< n`-truncation functor. See also the natural transformation `truncLTι`.
- `CategoryTheory.Triangulated.TStructure.truncGE` | module `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE` | package Mathlib | Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this is the `≥ n`-truncation functor. See also the natural transformation `truncGEπ`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `signedDist` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` (PhysLean)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `RigidBody.translational_equation_inertial` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `RigidBody.rotational_equation_inertial` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Turing.Dir.left` (Mathlib)
- `Lorentz.Velocity.pathFromZero` (PhysLean)
- `CategoryTheory.Arrow` (Mathlib)
- `CategoryTheory.Arrow.Hom.left` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `Lorentz.Velocity.zero` (PhysLean)
- `Partition.IsRepFun.apply_mem` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Mathlib.Tactic.Widget.subTriangle` (Mathlib)
- `CategoryTheory.Triangulated.TStructure.truncLT` (Mathlib)
- `CategoryTheory.Triangulated.TStructure.truncGE` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0523.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.FigureVelocityArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.MatchesProblemVelocityReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.MatchesSuppliedTruckBaseballFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.MatchesTruckBaseballScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.PrintedVelocityLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.SatisfiesGalileanVelocityComposition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.SignedVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.TruckBaseballFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0523.TruckBaseballRelativeMotionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
