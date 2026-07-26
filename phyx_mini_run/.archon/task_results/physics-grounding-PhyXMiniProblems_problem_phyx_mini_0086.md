# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0086.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0086.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:26ebaf8ebd6c6b589967bed83fe8e713b13ff9bd16023654dc46e7c6b1b19d43
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `Dim Time`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.T𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the time dimension.** The mass dimension component of the time dimension $T_d$ is equal to zero.

### Query: `Dim Speed Real`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `Real` | module `Mathlib.Data.Real.Basic` | package Mathlib | The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `nanosecond Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `UnitChoices.SIPrimed` | module `Physlib.Units.Basic` | package PhysLean | A `UnitChoices` which is related to `SI` by a prime scaling of each of the underlying units. This is useful in proving that a result is not dimensionally correct.
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).

### Query: `Optical Fiber Region`
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `Fiber Route`
- `Function.Fiber` | module `Mathlib.Logic.Function.FiberPartition` | package Mathlib | The indexing set of the partition.
- `FiberBundle.trivializationAt` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | Trivialization of a fiber bundle at a point.
- `FiberBundle` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the fibers are all homeomorphic to `F`, such that the local situation around each point is a direct product.

### Query: `Optical Fiber Pulse Setup`
- `Function.Fiber` | module `Mathlib.Logic.Function.FiberPartition` | package Mathlib | The indexing set of the partition.
- `FiberBundle.trivializationAt` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | Trivialization of a fiber bundle at a point.
- `FiberBundle` | module `Mathlib.Topology.FiberBundle.Basic` | package Mathlib | A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the fibers are all homeomorphic to `F`, such that the local situation around each point is a direct product.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `time In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit.hours_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Hours to Seconds.** The ratio of the time unit representing one hour to the time unit representing one second is equal to the non-negative real number $3600$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.T𝓭_mass` (PhysLean)
- `DimSpeed` (PhysLean)
- `Real` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `UnitChoices` (PhysLean)
- `UnitChoices.SIPrimed` (PhysLean)
- `TimeUnit.nanoseconds` (PhysLean)
- `Set.Ioi` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `Function.Fiber` (Mathlib)
- `FiberBundle.trivializationAt` (Mathlib)
- `FiberBundle` (Mathlib)
- `Function.Fiber` (Mathlib)
- `FiberBundle.trivializationAt` (Mathlib)
- `FiberBundle` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit.hours_div_seconds` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0086.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.DimSpeedReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.FiberRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.IsClosestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.MatchesOpticalFiberFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.OpticalFiberPulseSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.OpticalFiberRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0086.SatisfiesOpticalFiberLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
