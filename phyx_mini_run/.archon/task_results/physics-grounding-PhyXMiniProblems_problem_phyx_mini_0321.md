# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0321.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0321.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:52b876741a4fd55313a5779354362a5afb9343602d372097e2b2779f29a9d0b1
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Acoustic Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.
- `Composition.length` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | The length of a composition, i.e., the number of blocks in the composition.

### Query: `Acoustic Duration`
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `Dimension.L𝓭_time` | module `Physlib.Units.Dimension` | package PhysLean | **Time Component of the Length Dimension.** The time component of the length dimension is equal to zero.
- `TimeUnit.deciseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of deciseconds (10⁻¹ of a second).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `duration Readout`
- `linter.tacticAnalysis.tryAtEachStep.showTiming` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Whether to show timing information in "tryAtEachStep" tactic analysis output. When true (default), messages include elapsed time like `(23ms)`. Set to false in tests to avoid non-deterministic output.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `Computation.Results.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Resulting Computation.** If a terminating computation $s$ results in a value $a$ in exactly $n$ steps, then the length of the computation $s$ is equal to $n$.

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `duration In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `TimeUnit.minutes_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Minutes to Seconds.** The ratio of the time unit for minutes to the time unit for seconds is equal to the non-negative real number $60$.
- `TimeUnit.days_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Days to Seconds.** The ratio of the time unit representing one day to the time unit representing one second is equal to $86400$.

### Query: `speed In Meters Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Sac Boundary`
- `SSet.boundary` | module `Mathlib.AlgebraicTopology.SimplicialSet.Boundary` | package Mathlib | The boundary `∂Δ[n]` of the `n`-th standard simplex consists of all `m`-simplices of `stdSimplex n` that are not surjective (when viewed as monotone function `m → n`).
- `Polygon.boundary` | module `Mathlib.Geometry.Polygon.Basic` | package Mathlib | The boundary of the polygon is the union of all its edges.
- `Coheyting.boundary` | module `Mathlib.Order.Heyting.Boundary` | package Mathlib | The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with itself. Note that this is always `⊥` for a Boolean algebra.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `Cycle.length` (Mathlib)
- `Composition.length` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Dimension.L𝓭_time` (PhysLean)
- `TimeUnit.deciseconds` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `linter.tacticAnalysis.tryAtEachStep.showTiming` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `Computation.Results.length` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `TimeUnit.minutes_div_seconds` (PhysLean)
- `TimeUnit.days_div_seconds` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `SSet.boundary` (Mathlib)
- `Polygon.boundary` (Mathlib)
- `Coheyting.boundary` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0321.AcousticDuration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.AcousticLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.ClickMechanism`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.EchoRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.PropagationMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.SacBoundary`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.SatisfiesEchoRoundTripLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0321.SpermWhaleClickSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
