# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0331.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0331.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `Area Quantity`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `Heat Current Quantity`
- `Electromagnetism.CurrentDensity` | module `Physlib.Electromagnetism.Basic` | package PhysLean | Current density.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).

### Query: `Thermal Conductivity Quantity`
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `area In Square Meters`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.

### Query: `area In Square Centimeters`
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `heat Current In Watts`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `thermal Conductivity In Watts Per Meter Kelvin`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `TemperatureUnit.nanokelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees nanokelvin (10^(-9) kelvin).

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `DimArea` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimArea.are` (PhysLean)
- `Electromagnetism.CurrentDensity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `DimArea.squareMeter` (PhysLean)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.are` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `JoinedIn` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `JoinedIn` (Mathlib)
- `TemperatureUnit.nanokelvin` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0331.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.AreaQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.CompositeRodFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.CompositeRodSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.ContactQuality`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.FigureObject`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.HasPhysicalCompositeRodParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.HeatCurrentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.MatchesCompositeRodScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.MeasuredTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.RodMaterial`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.RodSection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.RodSideCondition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.RoundsToDisplayedMillimeter`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.SatisfiesInsulatedSteadyFourierConduction`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.SatisfiesKelvinCelsiusCalibration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.SatisfiesPerfectThermalContactLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.ThermalConductivityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.ThermalContact`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.ThermalLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.ThermalRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.UsesAtmosphericWaterFixedPoints`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.UsesTextbookThermalConductivities`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0331.WaterPressureRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
