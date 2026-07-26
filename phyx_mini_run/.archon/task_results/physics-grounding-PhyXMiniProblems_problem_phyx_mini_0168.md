# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0168.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0168.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9eba3a5e597a5cb3425a7bc0d7b2377b8d3960053330b42516a8e82688f95d40
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

### Query: `Acoustic Speed`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `meters Value`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.

### Query: `seconds Value`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `TimeUnit.weeks_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Weeks to Seconds.** The ratio of the time unit of one week to the time unit of one second is equal to $604,800$.
- `TimeUnit.minutes_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Minutes to Seconds.** The ratio of the time unit for minutes to the time unit for seconds is equal to the non-negative real number $60$.

### Query: `meters Per Second Value`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of One Meter per Second to Miles per Hour.** One meter per second is equal to $\frac{3125}{1397}$ times one mile per hour.

### Query: `Sound Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Sym2.sound` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | **Equality of Unordered Pairs.** For any elements $a, b, c, d$ in a type $\alpha$, if the pair $(a, b)$ is related to the pair $(c, d)$ by the equivalence relation defining unordered pairs, then the corresponding unor...
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` | module `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | package Mathlib | **Middle Object of the Short Complex $L_2'$.** The middle object of the short complex $L_2'$ is defined as the first object of the short complex $L_3$ in the given snake input.

### Query: `Sound Path Leg`
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space
- `Quotient.sound'` | module `Mathlib.Data.Quot` | package Mathlib | **Soundness of the Quotient Map.** For any two elements $a$ and $b$ of a type equipped with an equivalence relation, if $a$ is related to $b$, then their images under the canonical projection to the quotient are equal.
- `allFilePaths` | module `Physlib.Meta.AllFilePaths` | package PhysLean | Gets an array of all file paths in `Physlib`.

### Query: `Boat Horn Diver Setup`
- `SSet.horn` | module `Mathlib.AlgebraicTopology.SimplicialSet.Horn` | package Mathlib | `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`. It consists of all `m`-simplices `α` of `Δ[n]` for which the union of `{i}` and the range of `α` is not all of `n` (when view...
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `SSet.horn_ι_mem_innerHornInclusions` | module `Mathlib.AlgebraicTopology.Quasicategory.InnerFibration` | package Mathlib | **Inner Horn Inclusions.** For any $n \in \mathbb{N}$ and any $i \in \{0, \dots, n\}$, if $0 < i < n$, then the inclusion of the horn $\Lambda^n_i \hookrightarrow \Delta^n$ is an inner horn inclusion.

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
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `TimeUnit.weeks_div_seconds` (PhysLean)
- `TimeUnit.minutes_div_seconds` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_eq_mul_oneMilePerHour` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Sym2.sound` (Mathlib)
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` (Mathlib)
- `Path` (Mathlib)
- `Quotient.sound'` (Mathlib)
- `allFilePaths` (PhysLean)
- `SSet.horn` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `SSet.horn_ι_mem_innerHornInclusions` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0168.AcousticDuration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.AcousticLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.AcousticSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.BoatHornDiverSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.IsClosestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.MatchesSoundSpeedDataAt20C`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.SatisfiesSoundPropagationLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.SoundMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0168.SoundPathLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
