# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0529.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0529.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1b886a04d128b7d9eb4ae6b9bb5ed0838a3774ede5536de175652e324f4fcbe8
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

### Query: `Duration Quantity`
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.
- `Dimension.L𝓭_time` | module `Physlib.Units.Dimension` | package PhysLean | **Time Component of the Length Dimension.** The time component of the length dimension is equal to zero.
- `Dimensionful.ext` | module `Physlib.Units.Basic` | package PhysLean | **Extensionality of Dimensionful Quantities.** Two dimensionful quantities associated with a type that carries a dimension are equal if their underlying values are equal.

### Query: `Axial Coordinate`
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `WeierstrassCurve.Affine.Point.xRep_zero` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` | package Mathlib | **Projective Representative of the Zero Point's x-coordinate.** The projective representative of the $x$-coordinate for the zero point on an affine Weierstrass curve is given by the vector $[1, 0]$.

### Query: `Clock Coordinate`
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `RigidBody.coordinate_system` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z) and a moving system (x₁,x₂,x₃) rigidly attached to the body.
- `LipschitzOnWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Components in $\ell^\infty$.** A function $f$ mapping from a pseudometric space to the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ on...

### Query: `Axial Velocity`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.velocityClosedForm_val` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The closed-form velocity as a plain vector-valued function of the coordinates of `y`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `duration Readout`
- `linter.tacticAnalysis.tryAtEachStep.showTiming` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Whether to show timing information in "tryAtEachStep" tactic analysis output. When true (default), messages include elapsed time like `(23ms)`. Set to false in tests to avoid non-deterministic output.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `Computation.Results.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Resulting Computation.** If a terminating computation $s$ results in a value $a$ in exactly $n$ steps, then the length of the computation $s$ is equal to $n$.

### Query: `axial Coordinate Readout`
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.coordinate_system` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z) and a moving system (x₁,x₂,x₃) rigidly attached to the body.

### Query: `clock Coordinate Readout`
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `RigidBody.coordinate_system` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z) and a moving system (x₁,x₂,x₃) rigidly attached to the body.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `Dimension.L𝓭_time` (PhysLean)
- `Dimensionful.ext` (PhysLean)
- `LipschitzWith.coordinate` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `WeierstrassCurve.Affine.Point.xRep_zero` (Mathlib)
- `LipschitzWith.coordinate` (Mathlib)
- `RigidBody.coordinate_system` (PhysLean)
- `LipschitzOnWith.coordinate` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.velocityClosedForm_val` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `linter.tacticAnalysis.tryAtEachStep.showTiming` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Computation.Results.length` (Mathlib)
- `LipschitzWith.coordinate` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.coordinate_system` (PhysLean)
- `LipschitzWith.coordinate` (Mathlib)
- `RigidBody.coordinate_system` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0529.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.AxialCoordinate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.AxialDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.AxialVelocity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.CatchEvent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.ClockCoordinate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.CoordinateAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.DurationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.EdMeasuresGroundFrameElapsedTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.HasPhysicalRelativisticParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.MatchesDisplayedTimeChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.MatchesScenarioAndPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.ObserverLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.RelativisticCatchFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.RelativisticCatchSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.SatisfiesLorentzTimeTransformation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0529.SatisfiesUniformBallMotionInMovingFrame`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
