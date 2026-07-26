# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0669.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0669.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Axial Position`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Alignment.center` | module `Mathlib.Util.FormatTable` | package Mathlib | **Center Alignment.** A positioning mode within an alignment specification that indicates an item is centered horizontally within a given space.
- `QuantumMechanics.positionOperator_isSelfAdjoint` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | **Self-Adjointness of the Position Operator.** For any coordinate index $i$, the position operator $\mathcal{X}_i$ is a self-adjoint operator.

### Query: `Axial Velocity`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.velocityClosedForm_val` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The closed-form velocity as a plain vector-valued function of the coordinates of `y`.

### Query: `position In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `UnitExamples.meters400` | module `Physlib.Units.Examples` | package PhysLean | The length corresponding to 400 meters.

### Query: `velocity In Meters Per Second`
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Axis Quantity`
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `Axis Unit`
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `Spatial Axis`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `TimeAndSpace.snd_smul` | module `Physlib.SpaceAndTime.TimeAndSpace.EuclideanGroup.Action` | package PhysLean | The Euclidean-group action applies to the second coordinate.

### Query: `Trace Geometry`
- `Matrix.trace` | module `Mathlib.LinearAlgebra.Matrix.Trace` | package Mathlib | The trace of a square matrix. For more bundled versions, see: * `Matrix.traceAddMonoidHom` * `Matrix.traceLinearMap`
- `Algebra.trace_trace` | module `Mathlib.RingTheory.Trace.Defs` | package Mathlib | **Transitivity of the Algebraic Trace.** Let $R, S,$ and $T$ be commutative rings such that $S$ is an $R$-algebra and $T$ is an $S$-algebra (forming a scalar tower $R \to S \to T$). If $S$ is a free and finite $R$-mod...
- `Algebra.trace` | module `Mathlib.RingTheory.Trace.Defs` | package Mathlib | The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`, as an `R`-linear map.

### Query: `Figure Vertex`
- `VertexOperator` | module `Mathlib.Algebra.Vertex.VertexOperator` | package Mathlib | A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to Laurent series with coefficients in `V`. We write this as a specialization of the heterogeneous case.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Limits.Cocone.fromCostructuredArrow_pt` | module `Mathlib.CategoryTheory.Limits.ConeCategory` | package Mathlib | **The Vertex of a Cocone from a Diagram of Costructured Arrows.** Given a functor $F : \mathcal{C} \to \mathcal{D}$, an object $X$ in $\mathcal{D}$, and a diagram $G : J \to (F \downarrow X)$ in the category of costru...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Alignment.center` (Mathlib)
- `QuantumMechanics.positionOperator_isSelfAdjoint` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.velocityClosedForm_val` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `UnitExamples.meters400` (PhysLean)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `IsUnit` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `TimeAndSpace.snd_smul` (PhysLean)
- `Matrix.trace` (Mathlib)
- `Algebra.trace_trace` (Mathlib)
- `Algebra.trace` (Mathlib)
- `VertexOperator` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Limits.Cocone.fromCostructuredArrow_pt` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0669.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.AxialPosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.AxialVelocity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.AxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.AxisUnit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.FigureVertex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.IsStraightTraceSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.ParticleMotionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.PositionTimeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.SatisfiesAverageVelocityLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.SpatialAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0669.TraceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
