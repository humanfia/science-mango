# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0124.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0124.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:45ceb1cc2caad84fb7d418d98caac320e32771dcb6ade2d85704561d1cf0e28b
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

### Query: `Signed Length Quantity`
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `signed Length Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist_neg` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Negation of the Reference Vector in Signed Distance.** The signed distance from a point $p$ to a point $q$ with respect to the negation of a reference vector $v$ is equal to the negative of the signed distance from...

### Query: `time Readout`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeMan` | module `Physlib.SpaceAndTime.Time.TimeMan` | package PhysLean | The type `TimeMan` represents the time manifold. Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional structure.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist` (Mathlib)
- `LengthUnit` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `signedDist` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist_neg` (Mathlib)
- `Time` (PhysLean)
- `TimeMan` (PhysLean)
- `TimeUnit` (PhysLean)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0124.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.BarrierKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.BeamKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.DriveKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.FigurePointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.FullyClosedAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.IncidentSide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.LightColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.MatchesFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.MembraneLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.OpticalRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SatisfiesSlidingMembraneKinematics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SatisfiesSlitArrayInterferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.ScreenCenter`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.ScreenShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SignedLengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SlidingMembraneInterferenceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.SpotLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.VerticalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0124.WithinFirstApertureCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
