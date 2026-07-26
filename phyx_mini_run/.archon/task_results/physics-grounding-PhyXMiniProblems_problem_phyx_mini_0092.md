# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0092.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0092.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7e9d643ea944985c28af55d94184c585b4fc8d16ace76ccc6b6c967d6226ced0
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Optical Duration`
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `HahnSeries.le_order_smul` | module `Mathlib.RingTheory.HahnSeries.Addition` | package Mathlib | **Order of a Scaled Hahn Series.** For a scalar $r$ and a Hahn series $x$, if the scalar product $r \cdot x$ is non-zero, then the order of $x$ is less than or equal to the order of $r \cdot x$.
- `HahnSeries.support` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The support of a Hahn series is just the set of indices whose coefficients are nonzero. Notably, it is well-founded.

### Query: `Optical Speed`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.

### Query: `nanosecond Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `UnitChoices.SIPrimed` | module `Physlib.Units.Basic` | package PhysLean | A `UnitChoices` which is related to `SI` by a prime scaling of each of the underlying units. This is useful in proving that a result is not dimensionally correct.
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).

### Query: `Beam Branch`
- `Physlib.FourTree.Branch` | module `Physlib.Mathematics.DataStructures.FourTree.Basic` | package PhysLean | A branch has the data of a term of type `α2` and a multiset of type `Twig α3 α4`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Physlib.FourTree.Branch.mem` | module `Physlib.Mathematics.DataStructures.FourTree.Basic` | package PhysLean | An element of `a : α2 × α3 × α4` is a member of `Branch α2 α3 α4` if the underlying `α2` element of the `Branch` is `a.1` and `a.2` is a member of one of the `Twig`.

### Query: `Figure Landmark`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `CategoryTheory.Limits.WalkingSpan.right` | module `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan` | package Mathlib | The right point of the walking span.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Laser Block Delay Setup`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `Path.delayReflLeft` | module `Mathlib.Topology.Homotopy.HSpaces` | package Mathlib | This is the function on p. 475 of [serre1951], defining a homotopy from a path `γ` to the product path `e ∧ γ`.
- `Matrix.blockDiagonal` | module `Mathlib.Data.Matrix.Block` | package Mathlib | `Matrix.blockDiagonal M` turns a homogeneously-indexed collection of matrices `M : o → Matrix m n α'` into an `m × o`-by-`n × o` block matrix which has the entries of `M` along the diagonal and zero elsewhere. See als...

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `duration In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `TimeUnit.minutes_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Minutes to Seconds.** The ratio of the time unit for minutes to the time unit for seconds is equal to the non-negative real number $60$.
- `TimeUnit.days_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Days to Seconds.** The ratio of the time unit representing one day to the time unit representing one second is equal to $86400$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `HahnSeries.leadingCoeff` (Mathlib)
- `HahnSeries.le_order_smul` (Mathlib)
- `HahnSeries.support` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `UnitChoices` (PhysLean)
- `UnitChoices.SIPrimed` (PhysLean)
- `TimeUnit.nanoseconds` (PhysLean)
- `Physlib.FourTree.Branch` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Physlib.FourTree.Branch.mem` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `CategoryTheory.Limits.WalkingSpan.right` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Matrix.BlockTriangular` (Mathlib)
- `Path.delayReflLeft` (Mathlib)
- `Matrix.blockDiagonal` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `TimeUnit.minutes_div_seconds` (PhysLean)
- `TimeUnit.days_div_seconds` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0092.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.BeamBranch`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.FigureLandmark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.LaserBlockDelaySetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.OpticalDuration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.OpticalSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0092.SatisfiesOpticalDelayLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
