# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0591.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0591.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:30fced44492f4b8ab10c2901a4a65d063cc98548713781fac4fee09924a06ac3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Signed Axial Velocity`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `ComplexShape.ε` | module `Mathlib.Algebra.Homology.ComplexShapeSigns` | package Mathlib | The signs which appear in the vertical differential of the total complex.

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `signed Velocity Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | The trajectory resulting from `toInitialConditions` has the specified velocity `v_t₀` at time `t₀`.

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `vacuum Speed Of Light Readout`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `velocity In Light Speed Units`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `speed In Light Speed Units`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.

### Query: `Reference Frame Label`
- `Bundle.Trivialization.localFrame_coeff` | module `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame` | package Mathlib | Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i`. If x is outside of `e.baseSet`, this returns the junk value 0.
- `FrameHom` | module `Mathlib.Order.Hom.CompleteLattice` | package Mathlib | The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
- `Order.Frame` | module `Mathlib.Order.CompleteBooleanAlgebra` | package Mathlib | A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`.

### Query: `Geographic Pole`
- `stereoInvFun_ne_north_pole` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Inverse Stereographic Projection Avoids the North Pole.** For any unit vector $v$ in a real inner product space $E$, the inverse stereographic projection from the orthogonal complement of the span of $v$ into the un...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_C` | module `Mathlib.RingTheory.HahnSeries.Multiplication` | package Mathlib | **Order of a Constant Hahn Series.** For any element $r$ in a ring $R$, the order of the constant Hahn series $C(r)$ is equal to $0$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `signedDist` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `ComplexShape.ε` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `signedDist` (Mathlib)
- `Lorentz.Velocity` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.InitialConditionsAtTime.toInitialConditions_velocity_at_t₀` (PhysLean)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `LightProfinite` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `DimSpeed.speedOfLight` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `LightProfinite` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `Units` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `Bundle.Trivialization.localFrame_coeff` (Mathlib)
- `FrameHom` (Mathlib)
- `Order.Frame` (Mathlib)
- `stereoInvFun_ne_north_pole` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_C` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0591.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.AxialDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.CosmicRayApproachSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.CosmicRayAxisFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.CosmicRayParticle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.GeographicPole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.HasPhysicalCosmicRayParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.IsUniqueMatchingAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.MatchesEarthFrameVelocityReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.ObeysCollinearLorentzVelocityTransformation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.ReferenceFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.RelativeApproachSpeedIsMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.RoundsToNearestHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.SignedAxialVelocity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0591.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
