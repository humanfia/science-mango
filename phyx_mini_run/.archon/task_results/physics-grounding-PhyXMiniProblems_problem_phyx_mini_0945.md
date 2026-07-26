# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0945.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0945.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6ae6d5f458ce40bc5ae2efec0b32fd6c4c5c70979cbc2936f342683c32dc5df2
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `irradiance Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `ringKrullDim` | module `Mathlib.RingTheory.KrullDimension.Basic` | package Mathlib | The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `power Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `Irradiance Quantity`
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Radiant Power Quantity`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `QuantumMechanics.radiusPowOperator_hasDenseDomain` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | **Dense Domain of the Radial Power Operator.** For any real number $s$, the radial power operator $\mathcal{R}^s$ has a dense domain.

### Query: `area In Square Meters`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.

### Query: `irradiance In Watts Per Square Meter`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `power In Watts`
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `JoinedIn.joined` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | **Path Connectivity in a Subset Implies Path Connectivity.** If two points $x$ and $y$ in a topological space are joined by a path contained within a subset $F$, then they are joined by a path in the space.

### Query: `power In Kilowatts`
- `JoinedIn.joined` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | **Path Connectivity in a Subset Implies Path Connectivity.** If two points $x$ and $y$ in a topological space are joined by a path contained within a subset $F$, then they are joined by a path in the space.
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `Orbital Region`
- `MulAction.orbit` | module `Mathlib.GroupTheory.GroupAction.Defs` | package Mathlib | The orbit of an element under an action.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `ClassicalMechanics.VisViva.ConfigurationSpace` | module `Physlib.ClassicalMechanics.OrbitalMechanics.VisViva` | package PhysLean | Configuration space for orbital mechanics, defining the orbital radius.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `ringKrullDim` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `DimEnergy.kilowattHour` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `QuantumMechanics.radiusPowOperator_hasDenseDomain` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `DimArea.squareMeter` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `PowerSeries` (Mathlib)
- `JoinedIn.joined` (Mathlib)
- `JoinedIn.joined` (Mathlib)
- `PowerSeries` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `MulAction.orbit` (Mathlib)
- `regionBetween` (Mathlib)
- `ClassicalMechanics.VisViva.ConfigurationSpace` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0945.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.IrradianceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.IsUniqueMatchingAbsorbedPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.MatchesDisplayedAbsorbedPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.MatchesPrimarySatelliteFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.OrbitalRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.PanelWing`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.RadiantPowerQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.RadiationIncidence`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SatelliteSolarPanelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SatelliteSolarPowerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SatisfiesSolarPanelPowerLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SolarPanelArray`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SunSensorPurpose`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SunlightVectorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.SurfaceAbsorptionModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0945.UsesTextbookAverageNearEarthIrradiance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
