# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0748.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0748.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a3b8f727f55bac599acad2169ae8392f0cecd9bc93a17d63d160ece1463aad45
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

### Query: `Diagram Vector`
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Display the string diagram for a given term. Example usage: ``` /- String diagram for the equality theorem. -/ #string_diagram MonoidalCategory.whisker_exchange /- String diagram for the morphism. -/ variable {C : Typ...
- `Matrix.diagonal` | module `Mathlib.Data.Matrix.Diagonal` | package Mathlib | `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0` if `i ≠ j`. Note that bundled versions exist as: * `Matrix.diagonalAddMonoidHom` * `Matrix.diagonalLinearMap` * `Matrix.d...
- `LightDiagram` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | A structure containing the data of sequential limit in `Profinite` of finite sets.

### Query: `Distance Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Nat.instDist` | module `Mathlib.Topology.Instances.Nat` | package Mathlib | **Distance on Natural Numbers.** The distance between two natural numbers $x$ and $y$ is defined as the standard distance between them when they are considered as real numbers, denoted by $\text{dist}(x, y)$.
- `Int.dist_eq` | module `Mathlib.Topology.Instances.Int` | package Mathlib | **Distance Between Integers.** For any two integers $x$ and $y$, the distance between them, denoted $dist(x, y)$, is equal to the absolute value of their difference when considered as real numbers, $|x - y|$.

### Query: `Planar Position`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Orthogonality of Basis Charges and Even-Indexed Planes.** For any two distinct indices $k$ and $j$ in $\{0, \dots, n\}$, the $k$-th basis charge evaluated on the first vector of the $j$-th even plane is zero.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `Planar Velocity`
- `Lorentz.Velocity` | module `Physlib.Relativity.Tensors.RealTensor.Velocity.Basic` | package PhysLean | A Lorentz Velocity is a Lorentz vector which has norm equal to one and which is future-directed.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.transverseHarmonicPlaneWave_eq_planeWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | The transverse harmonic planewave representation is equivalent to the general planewave expression with `‖k‖ = ω/c`.

### Query: `kilometer Hour Units`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.

### Query: `distance In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Metric.infEDist` | module `Mathlib.Topology.MetricSpace.HausdorffDistance` | package Mathlib | The minimal edistance of a point to a set
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `speed In Kilometers Per Hour`
- `DimSpeed.oneMilePerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one mile per hour to SI units.** The value of one mile per hour, when expressed in the International System of Units (SI), is exactly $0.44704$ meters per second.
- `DimSpeed.oneKilometerPerHour` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 kilometer per hour.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.

### Query: `position In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `UnitExamples.meters400` | module `Physlib.Units.Examples` | package PhysLean | The length corresponding to 400 meters.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` (Mathlib)
- `Matrix.diagonal` (Mathlib)
- `LightDiagram` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Nat.instDist` (Mathlib)
- `Int.dist_eq` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `Lorentz.Velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.transverseHarmonicPlaneWave_eq_planeWave` (PhysLean)
- `Units` (Mathlib)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `Metric.infEDist` (Mathlib)
- `LengthUnit.miles` (PhysLean)
- `DimSpeed.oneMilePerHour_in_SI` (PhysLean)
- `DimSpeed.oneKilometerPerHour` (PhysLean)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `UnitExamples.meters400` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0748.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.DiagramVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.DistanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.HighwayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.IntersectingHighwaysSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.ObeysClassicalRelativeKinematics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.PlanarPosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.PlanarVelocity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0748.VehicleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
