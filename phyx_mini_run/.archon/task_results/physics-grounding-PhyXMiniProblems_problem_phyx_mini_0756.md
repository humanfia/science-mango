# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0756.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0756.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7907a1de4d1a4334f4b2b6d741994e65709761f60d9e4b59a060c1b2104e9506
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `force Dimension`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `Tire Plane`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `MSSMACC.planeY₃B₃` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3` | package PhysLean | The plane of linear solutions spanned by `Y₃`, `B₃` and `R`, a point orthogonal to `Y₃` and `B₃`.

### Query: `Planar Force Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `instCoeFunDimensionfulForallUnitChoices` | module `Physlib.Units.Basic` | package PhysLean | **Coercion of Dimensionful Quantities to Functions.** Any dimensionful quantity associated with a type $M$ that carries a dimension can be naturally treated as a function that maps a choice of units to an element of $M$.

### Query: `force Vector Readout`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `MeasureTheory.VectorMeasure.coe_mk` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | **Vector Measure Constructor Coercion.** Given a function $v$ from a collection of sets to a module $M$ and the necessary proofs $h_1, h_2, h_3$ that $v$ satisfies the axioms of a vector measure, the underlying functi...
- `ClassicalMechanics.HarmonicOscillator.force` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The force of the classical harmonic oscillator defined as `- dU(x)/dx` where `U(x)` is the potential energy.

### Query: `force Magnitude Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.

### Query: `force Magnitude In Newtons`
- `UnitExamples.NewtonsSecondWithDim` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim` with `.val`.
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` | module `Physlib.Electromagnetism.Kinematics.FieldStrength` | package PhysLean | The field strength from an electromagnetic potential, as a tensor `F^{μν}`.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `horizontal Component`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.
- `HomologicalComplex₂.d₁_eq` | module `Mathlib.Algebra.Homology.TotalComplex` | package Mathlib | **Horizontal Differential of a Total Complex.** For a bicomplex $K$ and a total complex shape $c_{12}$, the horizontal component of the differential $d_1$ from the object at index $(i_1, i_2)$ to the total complex obj...

### Query: `vertical Component`
- `connectedComponent` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | The connected component of a point is the maximal connected set that contains this point.
- `Complex.VerticalIntegrable` | module `Mathlib.Analysis.MellinTransform` | package Mathlib | A function `f` is `VerticalIntegrable` at `σ` if `y ↦ f(σ + yi)` is integrable.
- `CategoryTheory.NatTrans.vcomp_app` | module `Mathlib.CategoryTheory.NatTrans` | package Mathlib | **Components of Vertical Composition of Natural Transformations.** For any two natural transformations $\alpha: F \Rightarrow G$ and $\beta: G \Rightarrow H$ between functors $F, G, H: \mathcal{C} \to \mathcal{D}$, th...

### Query: `Puller`
- `Mathlib.Tactic.Push.PullTheorem` | module `Mathlib.Tactic.Push.Attr` | package Mathlib | A theorem for the `pull` tactic
- `CategoryTheory.IsPullback` | module `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs` | package Mathlib | The proposition that a square ``` P --fst--> X | | snd f | | v v Y ---g---> Z ``` is a pullback square. (Also known as a fibered product or Cartesian square.)
- `Mathlib.Tactic.Push.convPull____` | module `Mathlib.Tactic.Push` | package Mathlib | `pull c` rewrites the goal by pulling the constant `c` closer to the head of the expression. For instance, `pull _ ∈ _` rewrites `x ∈ y ∨ ¬ x ∈ z` into `x ∈ y ∪ zᶜ`. More precisely, the `pull` tactic repeatedly rewrit...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `UpperHalfPlane` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `MSSMACC.planeY₃B₃` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `instCoeFunDimensionfulForallUnitChoices` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `MeasureTheory.VectorMeasure.coe_mk` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.force` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `FluidDynamics.BodyForce` (PhysLean)
- `UnitExamples.NewtonsSecondWithDim` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` (PhysLean)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `connectedComponent` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)
- `HomologicalComplex₂.d₁_eq` (Mathlib)
- `connectedComponent` (Mathlib)
- `Complex.VerticalIntegrable` (Mathlib)
- `CategoryTheory.NatTrans.vcomp_app` (Mathlib)
- `Mathlib.Tactic.Push.PullTheorem` (Mathlib)
- `CategoryTheory.IsPullback` (Mathlib)
- `Mathlib.Tactic.Push.convPull____` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0756.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.FigureElement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.IsClosestDisplayedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.PlanarForceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.Puller`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.RoundsToNearestNewton`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.SatisfiesStationaryForceBalance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.TirePlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.TireTugSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0756.TugOfWarFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
