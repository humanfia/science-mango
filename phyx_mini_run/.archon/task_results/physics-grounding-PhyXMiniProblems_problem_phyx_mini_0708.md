# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0708.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0708.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:acdcba5aa841e3e1866c24c454f14f5da6efa3dd870fafc6e5babf7debe591dd
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

### Query: `Gravitational Constant Quantity`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `PureU1.ConstAbsSorted.not_hasBoundary_grav` | module `Physlib.QFT.QED.AnomalyCancellation.ConstAbs` | package PhysLean | **Gravitational Anomaly of Constant Absolute Value Charges without Boundary.** For a system of $n+1$ charges $S$ with constant absolute values and sorted components, if $S$ does not have a boundary, then the gravitati...
- `SMACCs.accGrav` | module `Physlib.Particles.StandardModel.AnomalyCancellation.Basic` | package PhysLean | The gravitational anomaly equation.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `mass In Kilograms`
- `MassUnit.kilograms` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The definition of a mass unit of kilograms.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.

### Query: `speed In Meters Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `gravitational Constant In SI`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `DimArea.hectare_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Hectare in SI Units.** In the SI unit system, the value of one hectare is exactly $10,000$.

### Query: `Celestial Body`
- `ConvexBody` | module `Mathlib.Analysis.Convex.Body` | package Mathlib | Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if it is convex, compact, and nonempty.
- `RigidBody.spherical_top` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | A spherical top is when all three of the principal moments of inertia are equal.
- `ConvexBody.convex` | module `Mathlib.Analysis.Convex.Body` | package Mathlib | **Convexity of a Convex Body.** Every convex body in a real topological vector space is a convex set.

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
- `LocallyConstant` (Mathlib)
- `PureU1.ConstAbsSorted.not_hasBoundary_grav` (PhysLean)
- `SMACCs.accGrav` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `MassUnit.kilograms` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `UnitChoices.SI_mass` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `LocallyConstant` (Mathlib)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `DimArea.hectare_in_SI` (PhysLean)
- `ConvexBody` (Mathlib)
- `RigidBody.spherical_top` (PhysLean)
- `ConvexBody.convex` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0708.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.CelestialBody`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.CentralBodyApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.EarthSunFallFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.EarthSunRadialFallSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.FallState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.GravitationalConstantQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.HasPhysicalEarthSunParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.InteractionModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.IsUniqueClosestImpactSpeedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.MatchesPrimaryEarthSunFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.MatchesStoppedEarthScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.RadialMotion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.SatisfiesNewtonianRadialFallEnergyLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.TrajectoryGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0708.UsesTextbookSolarParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
