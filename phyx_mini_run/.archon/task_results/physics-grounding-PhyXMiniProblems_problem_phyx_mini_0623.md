# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0623.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0623.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d217d4b1455f9cc2c12595f1e8033e7da009a31b53b1f85d4eb80566e5d62e90
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

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `momentum Dimension`
- `QuantumMechanics.momentumCLM` | module `Physlib.QuantumMechanics.Operators.Momentum` | package PhysLean | Component `i` of the momentum operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`.
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `QuantumMechanics.OneDimension.momentumOperator` | module `Physlib.QuantumMechanics.Operators.OneDimension.Momentum` | package PhysLean | The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking `ψ` to `- i ℏ ψ'`.

### Query: `Momentum Magnitude Quantity`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.linearMomentum_eq` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | **Linear Momentum of a Rigid Body.** For a rigid body in $d$-dimensional space, the linear momentum at any time $t$ is equal to the product of the body's total mass and the velocity of its center of mass at that time.

### Query: `action Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `WithDim.instMulActionNNReal` | module `Physlib.Units.WithDim.Basic` | package PhysLean | **Scalar Action on Dimension-Tagged Types.** Given a physical dimension $d$ and a type $M$ equipped with a scalar action of the nonnegative real numbers $\mathbb{R}_{\ge 0}$, the type of elements of $M$ tagged with di...

### Query: `Action Quantity`
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `Action` | module `Mathlib.CategoryTheory.Action.Basic` | package Mathlib | An `Action V G` represents a bundled action of the monoid `G` on an object of some category `V`. As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`, while when `V = Type` this is a `G`-...
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `QuantumMechanics.momentumCLM` (PhysLean)
- `Momentum` (PhysLean)
- `QuantumMechanics.OneDimension.momentumOperator` (PhysLean)
- `Momentum` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.linearMomentum_eq` (PhysLean)
- `Dimension` (PhysLean)
- `MulAction` (Mathlib)
- `WithDim.instMulActionNNReal` (PhysLean)
- `MulAction` (Mathlib)
- `Action` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0623.ActionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.ElectronSurfaceDiffractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.FigureBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.FigureLengthLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.HasPhysicalSurfaceDiffractionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.IncidenceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.IsUniqueMatchingDisplayedSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MatchesDisplayedSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MatchesElectronSurfaceDiffractionScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MatchesSuppliedSurfaceDiffractionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.MomentumMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.ParticleSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.RoundsToHundredthNanometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.SatisfiesElectronSurfaceDiffractionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.SurfaceDiffractionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.SurfaceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0623.UsesStandardElectronReferenceData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
