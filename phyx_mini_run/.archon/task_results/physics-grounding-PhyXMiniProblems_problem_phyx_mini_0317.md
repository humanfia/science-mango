# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0317.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0317.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:91ac5c49f84cf6f7ce3ee7faa5c560e7f4cd575c4fe7af6d076b46497a599333
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Acoustic Power Quantity`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `PowerBasis` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | `pb : PowerBasis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)` is a basis for the `R`-algebra `S` (viewed as `R`-module). This is a structure, not a class, since the same algebra can have many power bases....

### Query: `Acoustic Intensity Quantity`
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `DimArea.acre_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **The Value of an Acre in SI Units.** In the International System of Units (SI), the area of one acre is defined as exactly $4046.8564224$ square meters.
- `DimPressure.bar` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 bar (100,000 pascals).

### Query: `distance Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Real.dist_eq` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | **Distance on the Real Line.** For any two real numbers $x$ and $y$, the distance between them, denoted by $\text{dist}(x, y)$, is equal to the absolute value of their difference, $|x - y|$.
- `Nat.instDist` | module `Mathlib.Topology.Instances.Nat` | package Mathlib | **Distance on Natural Numbers.** The distance between two natural numbers $x$ and $y$ is defined as the standard distance between them when they are considered as real numbers, denoted by $\text{dist}(x, y)$.

### Query: `acoustic Power Readout`
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `TensorPower` | module `Mathlib.LinearAlgebra.TensorPower.Basic` | package Mathlib | Homogeneous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for `⨂[R] (i : Fin n), M`.
- `PowerBasis` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | `pb : PowerBasis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)` is a basis for the `R`-algebra `S` (viewed as `R`-module). This is a structure, not a class, since the same algebra can have many power bases....

### Query: `acoustic Intensity Readout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `distance In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Metric.infEDist` | module `Mathlib.Topology.MetricSpace.HausdorffDistance` | package Mathlib | The minimal edistance of a point to a set
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `acoustic Power In Watts`
- `JoinedIn.joined` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | **Path Connectivity in a Subset Implies Path Connectivity.** If two points $x$ and $y$ in a topological space are joined by a path contained within a subset $F$, then they are joined by a path in the space.
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `ArithmeticFunction.pow` | module `Mathlib.NumberTheory.ArithmeticFunction.Misc` | package Mathlib | `pow k n = n ^ k`, except `pow 0 0 = 0`.

### Query: `acoustic Intensity In Watts Per Square Meter`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.acre_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **The Value of an Acre in SI Units.** In the International System of Units (SI), the area of one acre is defined as exactly $4046.8564224$ square meters.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `PowerBasis` (Mathlib)
- `intervalIntegral` (Mathlib)
- `DimArea.acre_in_SI` (PhysLean)
- `DimPressure.bar` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Real.dist_eq` (Mathlib)
- `Nat.instDist` (Mathlib)
- `PowerSeries` (Mathlib)
- `TensorPower` (Mathlib)
- `PowerBasis` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `intervalIntegral` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Metric.infEDist` (Mathlib)
- `LengthUnit.miles` (PhysLean)
- `JoinedIn.joined` (Mathlib)
- `PowerSeries` (Mathlib)
- `ArithmeticFunction.pow` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.acre_in_SI` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0317.AcousticIntensityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.AcousticMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.AcousticPowerQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.AcousticSourceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.AtmosphericTwoSourceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.EmissionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.GraphAxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.HasPhysicalAcousticParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.IsClosestDisplayedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.MatchesAtmosphericSourceScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.MatchesProblemDistanceData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.MatchesSuppliedSoundLevelGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.RadialPosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.SatisfiesIsotropicInverseSquareLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.SoundLevelGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0317.UsesStandardSoundIntensityReference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
