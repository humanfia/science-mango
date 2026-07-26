# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0711.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0711.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:406febc7d0ebd6b17d26624ee75601a5990f5d1b27a687fc8fe651cb775fb8cb
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `rotation Frequency Dimension`
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `LorentzGroup.toRotation_continuous` | module `Physlib.Relativity.LorentzGroup.Restricted.FromBoostRotation` | package PhysLean | **Continuity of the Rotation Component of a Lorentz Transformation.** For any dimension $d$, the map that sends a restricted Lorentz transformation to its corresponding rotation component—defined by the product of the...
- `rotation` | module `Mathlib.Analysis.Complex.Isometry` | package Mathlib | An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by rotation.

### Query: `moment Of Inertia Dimension`
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `ProbabilityTheory.moment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment of a real random variable, `μ[X ^ p]`.
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.

### Query: `angular Momentum Dimension`
- `QuantumMechanics.angularMomentumOperator1D_trivial` | module `Physlib.QuantumMechanics.Operators.AngularMomentum` | package PhysLean | In one dimension the angular momentum operator is trivial.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `RigidBody.angularMomentum` | module `Physlib.ClassicalMechanics.RigidBody.AngularMomentum` | package PhysLean | The angular momentum `L = ∫ r × (ω × r) dm` of a rigid body rotating with angular velocity `ω` about its reference point (each body point at `r` moving with velocity `ω × r`). Its `i`-th component is `ρ` applied to th...

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Rotation Frequency Quantity`
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `rotation` | module `Mathlib.Analysis.Complex.Isometry` | package Mathlib | An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by rotation.
- `Orientation.rightAngleRotation` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation `J`). This automorphism squares to -1. We will define rotations in such a way that this automorphism is equal to rotatio...

### Query: `Moment Of Inertia Quantity`
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `RigidBody.solidSphere_inertiaTensor` | module `Physlib.ClassicalMechanics.RigidBody.SolidSphere` | package PhysLean | The moment of inertia tensor of a solid sphere through its center of mass is `2/5 m R^2 * I`.
- `ProbabilityTheory.moment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment of a real random variable, `μ[X ^ p]`.

### Query: `Angular Momentum Magnitude`
- `RigidBody.angularMomentum` | module `Physlib.ClassicalMechanics.RigidBody.AngularMomentum` | package PhysLean | The angular momentum `L = ∫ r × (ω × r) dm` of a rigid body rotating with angular velocity `ω` about its reference point (each body point at `r` moving with velocity `ω × r`). Its `i`-th component is `ρ` applied to th...
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `RigidBody.angular_momentum_about_point` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The total angular momentum about a point O is L = ∫ r × v dm. With v = V + ω × r about the centre of mass, L = R × (M V) + I_CM ω, where R is the centre of mass position.

### Query: `mass Readout`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Orientation.rotation` (Mathlib)
- `LorentzGroup.toRotation_continuous` (PhysLean)
- `rotation` (Mathlib)
- `Ideal.inertiaDeg` (Mathlib)
- `ProbabilityTheory.moment` (Mathlib)
- `Momentum` (PhysLean)
- `QuantumMechanics.angularMomentumOperator1D_trivial` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `RigidBody.angularMomentum` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Orientation.rotation` (Mathlib)
- `rotation` (Mathlib)
- `Orientation.rightAngleRotation` (Mathlib)
- `Ideal.inertiaDeg` (Mathlib)
- `RigidBody.solidSphere_inertiaTensor` (PhysLean)
- `ProbabilityTheory.moment` (Mathlib)
- `RigidBody.angularMomentum` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `RigidBody.angular_momentum_about_point` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0711.AngularMomentumMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.Configuration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.EndpointMass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.ExpandingRodFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.ExpandingTwoMassRodSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.ExpansionMechanism`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.HasPhysicalExpandingRodParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.IsUniqueClosestDisplayedRotationFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MatchesDisplayedRotationFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MatchesExpandingTwoMassRodScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MatchesSuppliedExpandingRodFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.MomentOfInertiaQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.RodMassModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.RotationAxisGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.RotationFrequencyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.SatisfiesAngularMomentumConservationDuringExpansion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.SatisfiesCenteredEndpointGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0711.SatisfiesTwoPointMassRigidRotationLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
