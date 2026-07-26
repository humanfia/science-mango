# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0107.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0107.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a81c774888d15ec46188d84b1bf9c0eb8537235e36bb7dd417b40842b580f64e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

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

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `time In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit.hours_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Hours to Seconds.** The ratio of the time unit representing one hour to the time unit representing one second is equal to the non-negative real number $3600$.

### Query: `speed In Meters Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
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
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit.hours_div_seconds` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0107.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.DimSpeedReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.FiberFigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.FiberFigureSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.MatchesBentFiberFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.MatchesCentimeterChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.MatchesTravelQuestion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.OpticalFiberSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.SatisfiesBentFiberGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.SatisfiesCriticalBendOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.SatisfiesHomogeneousPropagationLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0107.TravelRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
