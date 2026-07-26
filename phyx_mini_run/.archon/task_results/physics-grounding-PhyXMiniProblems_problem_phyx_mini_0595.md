# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0595.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0595.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2d1cc03bf9dea373229864ea2ec2bb446b64da958ac418481fdc51a3e6be016d
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

### Query: `vacuum Speed Of Light In Meters Per Second`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `Electromagnetism.FreeSpace.c` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | The speed of light in free space.

### Query: `velocity In Light Speed Units`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Reference Frame Label`
- `Bundle.Trivialization.localFrame_coeff` | module `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame` | package Mathlib | Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`. If x is outside of `e.baseSet`, this returns the junk value 0.
- `FrameHom` | module `Mathlib.Order.Hom.CompleteLattice` | package Mathlib | The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
- `Order.Frame` | module `Mathlib.Order.CompleteBooleanAlgebra` | package Mathlib | A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`.

### Query: `Velocity Axis Symbol`
- `Lorentz.Velocity.zero` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | The `Velocity d` which has all space components zero.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `GalileanGroup.one_velocity` | module `Physlib.SpaceAndTime.GalileanGroup.Basic` | package PhysLean | **Identity Velocity of the Galilean Group.** The velocity component of the identity element in the Galilean group is the zero vector.

### Query: `Horizontal Tick Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the horizontal identity 2-square.
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.

### Query: `Vertical Tick Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the vertical identity 2-square.
- `Complex.VerticalIntegrable` | module `Mathlib.Analysis.MellinTransform` | package Mathlib | A function `f` is `VerticalIntegrable` at `σ` if `y ↦ f(σ + yi)` is integrable.

### Query: `Trace Style`
- `Matrix.trace` | module `Mathlib.LinearAlgebra.Matrix.Trace` | package Mathlib | The trace of a square matrix. For more bundled versions, see: * `Matrix.traceAddMonoidHom` * `Matrix.traceLinearMap`
- `Mathlib.Linter.linter.style.whitespace` | module `Mathlib.Tactic.Linter.Whitespace` | package Mathlib | The `whitespace` linter emits a warning if * either a command does not start at the beginning of a line; * or the "hypotheses segment" of a declaration does not coincide with its pretty-printed version. In practice, t...
- `Mathlib.Linter.linter.style.show` | module `Mathlib.Tactic.Linter.Style` | package Mathlib | The "show" linter emits a warning if the `show` tactic changed the goal. `show` should only be used to indicate intermediate goal states for proof readability. When the goal is actually changed, `change` should be pre...

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
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `Electromagnetism.FreeSpace.c` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `LightProfinite` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `Bundle.Trivialization.localFrame_coeff` (Mathlib)
- `FrameHom` (Mathlib)
- `Order.Frame` (Mathlib)
- `Lorentz.Velocity.zero` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `GalileanGroup.one_velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` (Mathlib)
- `Complex.VerticalIntegrable` (Mathlib)
- `Matrix.trace` (Mathlib)
- `Mathlib.Linter.linter.style.whitespace` (Mathlib)
- `Mathlib.Linter.linter.style.show` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0595.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.HasPhysicalRelativisticParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.HorizontalTickLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.MatchesSuppliedVelocityGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.ObeysCollinearEinsteinVelocityTransformation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.ReferenceFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.RelativisticVelocityGraphSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.SignedVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.TraceStyle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.TraceTrend`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.VelocityAxisSymbol`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.VelocityTransformationFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0595.VerticalTickLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
