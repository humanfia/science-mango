# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0923.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0923.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:460c8ed55efa9612ff40601840b199dbfa9e33824a00c009c625e2b11d746aff
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

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `Hubble Rate Quantity`
- `Cosmology.FLRW.FriedmannEquation.hubbleConstant` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | The hubble constant defined in terms of the scale factor as `(dₜ a) / a`. The notation `H` is used for the `hubbleConstant`. Semiformal implementation note: Implement also scoped notation.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Cosmology.FLRW.FriedmannEquation.deriv_hubbleConstant_neg_iff` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | Pointwise: `∂ₜ H t < 0` iff `-1 < q t` (assuming `a` is twice differentiable at `t` and both `a t` and `∂ₜ a t` are nonzero).

### Query: `units With Length`
- `LengthUnit.astronomicalUnits` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of an astronomical unit (149,597,870,700 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `units With Time`
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `WithZero.unitsWithZeroEquiv` | module `Mathlib.Algebra.GroupWithZero.WithZero` | package Mathlib | Any group is isomorphic to the units of itself adjoined with `0`.

### Query: `units For Speed`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `HasUnitSpeedOn` | module `Mathlib.Analysis.ConstantSpeed` | package Mathlib | `f` has unit speed on `s` if it is linearly parameterized by `l = 1` on `s`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `time Readout`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeMan` | module `Physlib.SpaceAndTime.Time.TimeMan` | package PhysLean | The type `TimeMan` represents the time manifold. Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional structure.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `Cosmology.FLRW.FriedmannEquation.hubbleConstant` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Cosmology.FLRW.FriedmannEquation.deriv_hubbleConstant_neg_iff` (PhysLean)
- `LengthUnit.astronomicalUnits` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `TimeUnit` (PhysLean)
- `Units` (Mathlib)
- `WithZero.unitsWithZeroEquiv` (Mathlib)
- `Units` (Mathlib)
- `HasUnitSpeedOn` (Mathlib)
- `DimSpeed` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `Time` (PhysLean)
- `TimeMan` (PhysLean)
- `TimeUnit` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0923.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.HasPhysicalExpansionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.HubblePlot`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.HubbleRateHasAlwaysBeenConstant`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.HubbleRateQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.MatchesDisplayedBillionYearPrecision`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.MatchesHubblePlotFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.PlotAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.PlotFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.RoundsToNearestBillionYears`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.SatisfiesHubbleLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.SatisfiesHubbleTimeAgeModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0923.UniverseExpansionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
