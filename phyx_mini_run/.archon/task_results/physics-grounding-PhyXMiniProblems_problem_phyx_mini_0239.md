# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0239.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0239.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7681c3e82bdbb13769767847263333a44479bbb8e2b93d157b50f95d72bc7e0e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `speed In Kilometers Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneKilometerPerHour_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Conversion of one kilometer per hour to SI units.** The value of one kilometer per hour, when expressed in the International System of Units (SI), is equal to $\frac{5}{18}$ meters per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `distance In Kilometers`
- `LengthUnit.kilometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of kilometers (10³ meters).
- `Metric.infEDist` | module `Mathlib.Topology.MetricSpace.HausdorffDistance` | package Mathlib | The minimal edistance of a point to a set
- `Int.instDist` | module `Mathlib.Topology.Instances.Int` | package Mathlib | **Distance on the Integers.** The distance between two integers $x$ and $y$ is defined as the standard Euclidean distance between them when they are embedded in the real numbers, denoted by $\text{dist}(x, y)$.

### Query: `vertical Coordinate In Kilometers`
- `LengthUnit.kilometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of kilometers (10³ meters).
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `Combinatorics.Line.vertical` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`.

### Query: `Is On Local Earth Surface`
- `IsLocalMaxOn` | module `Mathlib.Topology.Order.LocalExtr` | package Mathlib | `IsLocalMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`.
- `IsLocalMax.on` | module `Mathlib.Topology.Order.LocalExtr` | package Mathlib | **Local Maximum on a Subset.** If a function $f$ has a local maximum at a point $a$, then for any set $s$, $f$ also has a local maximum at $a$ when restricted to $s$.
- `IsLocalMinOn` | module `Mathlib.Topology.Order.LocalExtr` | package Mathlib | `IsLocalMinOn f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`.

### Query: `Is Underground`
- `IsAzumaya` | module `Mathlib.Algebra.Azumaya.Defs` | package Mathlib | An Azumaya algebra is a finitely generated, projective and faithful R-algebra where `AlgHom.mulLeftRight R A : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A` is an isomorphism.
- `IsClosed` | module `Mathlib.Topology.Defs.Basic` | package Mathlib | A set is closed if its complement is open
- `IsConnected` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | A connected set is one that is nonempty and where there is no non-trivial open partition.

### Query: `Seismic Wave Kind`
- `ClassicalMechanics.harmonicWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`.
- `ClassicalMechanics.WaveVector` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | The wavevector which indicates a direction and has magnitude `2π/λ`.
- `ClassicalMechanics.transverseHarmonicPlaneWave_eq_planeWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | The transverse harmonic planewave representation is equivalent to the general planewave expression with `‖k‖ = ω/c`.

### Query: `Wave Polarization`
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX_polarization_ellipse` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | **Polarization Ellipse Equation for a Harmonic Plane Wave.** For a harmonic electromagnetic plane wave propagating in the $x$-direction with wave number $k \neq 0$, amplitudes $E_{0,i} \neq 0$, and phases $\phi_i$ for...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.transverseHarmonicPlaneWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | Transverse monochromatic time-harmonic plane wave where the direction of propagation is taken to be `EuclideanSpace.single 2 1`. `f₀x` and `f₀y` are the respective amplitudes, `ω` is the angular frequency, `δx` and `δ...

### Query: `Earth Material Model`
- `Manifold.Elab.FindModelResult` | module `Mathlib.Geometry.Manifold.Notation` | package Mathlib | Information about a model with corners found through `findModelInner`. It includes the model with corners found, and, if this model is the trivial model with corners on a normed space, information about that normed sp...
- `modelWithCornersSelf` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace.
- `Matroid.IsLoop` | module `Mathlib.Combinatorics.Matroid.Loop` | package Mathlib | A 'loop' is a member of the closure of the empty set

### Query: `Propagation Path Model`
- `Path` | module `Mathlib.Topology.Path` | package Mathlib | Continuous path connecting two points `x` and `y` in a topological space
- `Path.ext` | module `Mathlib.Topology.Path` | package Mathlib | **Extensionality of Paths.** Two paths $\gamma_1, \gamma_2$ from $x$ to $y$ in a topological space $X$ are equal if their underlying functions from the unit interval $I$ to $X$ are equal.
- `Path.segment` | module `Mathlib.Analysis.Convex.PathConnected` | package Mathlib | The path from `a` to `b` going along a straight line segment

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneKilometerPerHour_in_SI` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `LengthUnit.kilometers` (PhysLean)
- `Metric.infEDist` (Mathlib)
- `Int.instDist` (Mathlib)
- `LengthUnit.kilometers` (PhysLean)
- `JoinedIn` (Mathlib)
- `Combinatorics.Line.vertical` (Mathlib)
- `IsLocalMaxOn` (Mathlib)
- `IsLocalMax.on` (Mathlib)
- `IsLocalMinOn` (Mathlib)
- `IsAzumaya` (Mathlib)
- `IsClosed` (Mathlib)
- `IsConnected` (Mathlib)
- `ClassicalMechanics.harmonicWave` (PhysLean)
- `ClassicalMechanics.WaveVector` (PhysLean)
- `ClassicalMechanics.transverseHarmonicPlaneWave_eq_planeWave` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX_polarization_ellipse` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.transverseHarmonicPlaneWave` (PhysLean)
- `Manifold.Elab.FindModelResult` (Mathlib)
- `modelWithCornersSelf` (Mathlib)
- `Matroid.IsLoop` (Mathlib)
- `Path` (Mathlib)
- `Path.ext` (Mathlib)
- `Path.segment` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0239.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.CandidateFitsStationReadings`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.CandidateFocus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.DetectionStation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.EarthMaterialModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.EarthquakeLocalizationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.HasNondegenerateStationGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.IsMinimumDetectionStationCount`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.IsOnLocalEarthSurface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.IsUnderground`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.MatchesProblemWaveData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.MatchesStationCountChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.MatchesSuppliedEarthquakeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.PropagationPathModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.SatisfiesStraightUniformSeismicPropagation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.SeismicWaveKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.StationSetLocatesFocusUnambiguously`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0239.WavePolarization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
