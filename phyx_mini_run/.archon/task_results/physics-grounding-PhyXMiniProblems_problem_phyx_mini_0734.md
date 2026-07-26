# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0734.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0734.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:336f99341327d59a2cec9e2036c10cb87aacd98623e657393041c909f4b195a5
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Planar Position Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Orthogonality of Basis Charges and Even-Indexed Planes.** For any two distinct indices $k$ and $j$ in $\{0, \dots, n\}$, the $k$-th basis charge evaluated on the first vector of the $j$-th even plane is zero.
- `PureU1.VectorLikeEvenPlane.P_evenFst` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Projection onto the First Basis Element of an Even Plane.** For any charge distribution $f$ indexed by $\{0, \dots, n\}$ and any index $j$, the linear functional $P$ evaluated at the $j$-th basis vector of the even...

### Query: `position Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `Trail Section Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `SimpleGraph.Walk.IsTrail` | module `Mathlib.Combinatorics.SimpleGraph.Paths` | package Mathlib | A *trail* is a walk with no repeating edges.
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...

### Query: `Entry Point Label`
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

### Query: `answer Angle Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | If the angle ∠ABC at a point is π, the angle ∠BCA is 0.

### Query: `Ant Trail Diagram`
- `LightDiagram` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | A structure containing the data of sequential limit in `Profinite` of finite sets.
- `Antitone` | module `Mathlib.Order.Monotone.Defs` | package Mathlib | A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`.
- `List.Nat.antidiagonal` | module `Mathlib.Data.List.NatAntidiagonal` | package Mathlib | The antidiagonal of a natural number `n` is the list of pairs `(i, j)` such that `i + j = n`.

### Query: `section Displacement Readout`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `FieldSpecification.CrAnSection` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.CrAnSection` | package PhysLean | The sections in `𝓕.CrAnFieldOp` over a list `φs : List 𝓕.FieldOp`. In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate each field as a `creation` or an `annilation` operator. E.g. th...
- `EuclideanGroup.rotation_smul_vsub_origin` | module `Physlib.SpaceAndTime.Space.EuclideanGroup.Action` | package PhysLean | A rotation acts on the displacement from the origin by its orthogonal part, for every `p`: `(r • p) -ᵥ origin = Q • (p -ᵥ origin)`.

### Query: `section Displacement Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `FieldSpecification.CrAnSection` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.CrAnSection` | package PhysLean | The sections in `𝓕.CrAnFieldOp` over a list `φs : List 𝓕.FieldOp`. In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate each field as a `creation` or an `annilation` operator. E.g. th...
- `Affine.Simplex.centroid_vsub_eq` | module `Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid` | package Mathlib | The vector from any point to the centroid is the average of vectors to the simplex vertices.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` (PhysLean)
- `PureU1.VectorLikeEvenPlane.P_evenFst` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `SimpleGraph.Walk.IsTrail` (Mathlib)
- `StateT.mkLabel` (Mathlib)
- `OnePoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right` (Mathlib)
- `LightDiagram` (Mathlib)
- `Antitone` (Mathlib)
- `List.Nat.antidiagonal` (Mathlib)
- `RigidBodyMotion.displacement` (PhysLean)
- `FieldSpecification.CrAnSection` (PhysLean)
- `EuclideanGroup.rotation_smul_vsub_origin` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `FieldSpecification.CrAnSection` (PhysLean)
- `Affine.Simplex.centroid_vsub_eq` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0734.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.AntTrailDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.EntryPointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.IsSymmetricSixtyDegreeBifurcation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.MatchesAntTrailFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.PlanarPositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.SectionsFormBifurcation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.SymmetricTrailBranchingLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0734.TrailSectionLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
