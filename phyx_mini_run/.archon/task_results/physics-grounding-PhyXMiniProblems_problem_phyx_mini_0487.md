# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0487.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0487.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:feb840714fa51ad9c4d84bf9c98b0799feefd7d389bf4eae71d6859a90dc4a89
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

### Query: `Areal Thermal Resistance Quantity`
- `TemperatureUnit.self_div_scale` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | **Ratio of a Temperature Unit to its Scaled Version.** For any temperature unit $x$ and any positive real number $r$, the ratio of $x$ to the unit obtained by scaling $x$ by a factor of $r$ is equal to the non-negativ...
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `area Readout`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `length In Inches`
- `LengthUnit.inches` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of inch (0.0254 meters).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `area In Square Feet`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.acre_eq_mul_squareFeet` | module `Physlib.Units.WithDim.Area` | package PhysLean | One acre is exactly `43560` square feet.
- `DimArea.squareFoot` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square foot.

### Query: `heat Current In Watts`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

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
- `TemperatureUnit.self_div_scale` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `DimArea` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimArea.are` (PhysLean)
- `LengthUnit.inches` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.acre_eq_mul_squareFeet` (PhysLean)
- `DimArea.squareFoot` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `JoinedIn` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0487.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.AreaQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.ArealThermalResistanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.CompositeWallFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.CompositeWallSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.ConductionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.DominantHeatTransferPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.HasPhysicalCompositeWallParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.HeatCurrentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.HeatFlowDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.MatchesCompositeWallScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.MeasuredTemperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.RoundsToNearestFiftyBtuPerHour`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.SatisfiesSeriesArealResistanceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.SatisfiesSteadySeriesWallHeatLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.UsesTextbookFourInchBrickResistance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.WallBoundary`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.WallLayer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0487.WallMaterial`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
