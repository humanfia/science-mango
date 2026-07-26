# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0710.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0710.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:dd9c38de4c47edf4b531202a0613efd463999325ea0b9b5ed29044c14d26d158
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

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Force Magnitude Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.
- `instCoeFunDimensionfulForallUnitChoices` | module `Physlib.Units.Basic` | package PhysLean | **Coercion of Dimensionful Quantities to Functions.** Any dimensionful quantity associated with a type $M$ that carries a dimension can be naturally treated as a function that maps a choice of units to an element of $M$.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `force Magnitude In Newtons`
- `UnitExamples.NewtonsSecondWithDim` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim` with `.val`.
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` | module `Physlib.Electromagnetism.Kinematics.FieldStrength` | package PhysLean | The field strength from an electromagnetic potential, as a tensor `F^{μν}`.
- `UnitExamples.NewtonsSecondWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim`.

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Can Shape`
- `CanLift` | module `Mathlib.Tactic.Lift` | package Mathlib | A class specifying that you can lift elements from `α` to `β` assuming `cond` is true. Used by the tactic `lift`.
- `Mathlib.Tactic.MkIff.Shape` | module `Mathlib.Tactic.MkIffOfInductiveProp` | package Mathlib | Auxiliary data associated with a single constructor of an inductive declaration.
- `CategoryTheory.Limits.WidePushoutShape` | module `Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks` | package Mathlib | A wide pushout shape for any type `J` can be written simply as `Option J`.

### Query: `Can Mass Distribution`
- `CanLift` | module `Mathlib.Tactic.Lift` | package Mathlib | A class specifying that you can lift elements from `α` to `β` assuming `cond` is true. Used by the tactic `lift`.
- `RigidBodyMotion.massDistribution` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The mass distribution of the rigid body in motion at time `t`: the pushforward of the body-fixed mass distribution along the rigid displacement, acting on a test function `f` by `f ↦ ρ (f ∘ displacement t)`.
- `RigidBodyMotion.massDistribution_mass` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The motion preserves the total mass: the mass distribution at any time `t` has the same total mass as the body.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `FluidDynamics.BodyForce` (PhysLean)
- `dimH` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `instCoeFunDimensionfulForallUnitChoices` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `UnitExamples.NewtonsSecondWithDim` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` (PhysLean)
- `UnitExamples.NewtonsSecondWithDim'` (PhysLean)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `CanLift` (Mathlib)
- `Mathlib.Tactic.MkIff.Shape` (Mathlib)
- `CategoryTheory.Limits.WidePushoutShape` (Mathlib)
- `CanLift` (Mathlib)
- `RigidBodyMotion.massDistribution` (PhysLean)
- `RigidBodyMotion.massDistribution_mass` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0710.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.CanMassDistribution`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.CanOnInclineSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.CanOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.CanPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.CanShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.FigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.ForceMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.GravitationalForce`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.HasPhysicalCanParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.IsClosestDisplayedHeight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.IsTallestStableHeight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.IsUniqueClosestDisplayedHeight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.MatchesCanOnInclineScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.MatchesCanProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.MatchesSuppliedCanFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.SatisfiesCenteredCanGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.SatisfiesLimitingLineOfActionGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.SatisfiesStaticStabilityLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.SuppliedCanFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.SupportSurfaceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0710.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
