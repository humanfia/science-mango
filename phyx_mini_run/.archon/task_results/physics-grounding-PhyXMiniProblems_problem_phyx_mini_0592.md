# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0592.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0592.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:922f050da16a7600651f64358bc390301e922e39779304efde254889489ea949
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Spatial Separation`
- `SeparationQuotient` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov quotient. This quotient is guaranteed to be a T₀ space.
- `Cosmology.SpatialGeometry` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)`
- `TotallySeparatedSpace` | module `Mathlib.Topology.Connected.TotallyDisconnected` | package Mathlib | A space is totally separated if any two points can be separated by two disjoint open sets covering the whole space.

### Query: `Time Interval`
- `IntervalIntegrable` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these intervals is always empty, so this...
- `Interval` | module `Mathlib.Order.Interval.Basic` | package Mathlib | The closed intervals in an order. We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`. To convert intervals to the set of elements between these endpoints, use the coercion...
- `MeasureTheory.hittingBtwn_le_iff_of_exists` | module `Mathlib.Probability.Process.HittingTime` | package Mathlib | **Characterization of Hitting Time in an Interval.** Let $\iota$ be a well-founded linearly ordered set. For a process $u$, a set $s$, and an index $\omega$, suppose there exists some time $j$ in the closed interval $...

### Query: `Speed Magnitude`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SpeedOfLight.val_pos` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | **Positivity of the Speed of Light.** The real-valued magnitude of the speed of light is strictly positive.

### Query: `meter Nanosecond Units`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).

### Query: `separation In Meters`
- `SeparationQuotient` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov quotient. This quotient is guaranteed to be a T₀ space.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Metric.AreSeparated` | module `Mathlib.Topology.MetricSpace.MetricSeparated` | package Mathlib | Two sets in an (extended) metric space are called *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant.

### Query: `time Interval In Nanoseconds`
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).
- `Interval` | module `Mathlib.Order.Interval.Basic` | package Mathlib | The closed intervals in an order. We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`. To convert intervals to the set of elements between these endpoints, use the coercion...
- `Turing.TM2ComputableInTime` | module `Mathlib.Computability.TuringMachine.Computable` | package Mathlib | A Turing machine + a time function + a proof it outputs `f` in at most `time(input.length)` steps.

### Query: `speed In Meters Per Nanosecond`
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.
- `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of One Meter per Second to Miles per Hour.** One meter per second is equal to $\frac{3125}{1397}$ times one mile per hour.

### Query: `vacuum Light Speed In Meters Per Nanosecond`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `Electromagnetism.EMSystem.c` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The speed of light.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.

### Query: `time Interval Of Nanoseconds`
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `Interval` | module `Mathlib.Order.Interval.Basic` | package Mathlib | The closed intervals in an order. We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`. To convert intervals to the set of elements between these endpoints, use the coercion...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `SeparationQuotient` (Mathlib)
- `Cosmology.SpatialGeometry` (PhysLean)
- `TotallySeparatedSpace` (Mathlib)
- `IntervalIntegrable` (Mathlib)
- `Interval` (Mathlib)
- `MeasureTheory.hittingBtwn_le_iff_of_exists` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `SpeedOfLight.val_pos` (PhysLean)
- `Units` (Mathlib)
- `DimArea.squareMeter` (PhysLean)
- `TimeUnit.nanoseconds` (PhysLean)
- `SeparationQuotient` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Metric.AreSeparated` (Mathlib)
- `TimeUnit.nanoseconds` (PhysLean)
- `Interval` (Mathlib)
- `Turing.TM2ComputableInTime` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `Electromagnetism.EMSystem.c` (PhysLean)
- `SpeedOfLight` (PhysLean)
- `TimeUnit.nanoseconds` (PhysLean)
- `intervalIntegral` (Mathlib)
- `Interval` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0592.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.AxialDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.GraphAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.GraphAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.HasPhysicalRelativisticParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.InertialFrameLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.IsNearestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.MatchesDisplayedPrecision`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.MatchesRelativisticSeparationScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.MatchesSuppliedSeparationTimeGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.PlottedCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.RelativisticSeparationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.SatisfiesInverseLorentzSpatialTransformation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.SeparationTimeGraphFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.SpatialSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.SpeedMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.TimeInterval`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0592.VerticalScaleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
