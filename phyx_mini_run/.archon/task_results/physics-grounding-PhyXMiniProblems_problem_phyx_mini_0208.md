# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0208.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0208.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:47db5f3076adfe3fbac21cd192c0156e440e69d4a90c9b7385f9ec6cda816480
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | The characteristic length `ξ` of the harmonic oscillator is defined as `√(ℏ /(m ω))`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Wave Number Quantity`
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone.
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Exponential Property of the Quanta Wave Number.** For any site index $n \in \{0, \dots, N-1\}$ and any quanta wave number $k$, the complex exponential of $i \cdot k \cdot (n+1) \cdot a$ is equal to the product of th...
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Quantized Wave Number Periodic Identity.** For any natural number $n$ and any quantized wave number $k$ associated with a tight-binding chain of $N$ sites and lattice constant $a$, the complex exponential $\exp(i k...

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `wave Number Readout`
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone.
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | The electromagnetic potential for a Harmonic wave travelling in the `x`-direction with wave number `k`.
- `ClassicalMechanics.planeWave` | module `Physlib.ClassicalMechanics.WaveEquation.Basic` | package PhysLean | A vector-valued plane wave travelling in the direction of `s` with propagation speed `c`.

### Query: `String Endpoint`
- `AddCircle.EndpointIdent` | module `Mathlib.Topology.Instances.AddCircle.Defs` | package Mathlib | The relation identifying the endpoints of `Icc a (a + p)`.
- `segment_inter_eq_endpoint_of_linearIndependent_of_ne` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Intersection of Segments with a Common Endpoint and Linearly Independent Directions.** Let $E$ be a module over an ordered domain $\mathbb{k}$. Suppose $x, y \in E$ are linearly independent. For any $c \in E$ and di...
- `segment_inter_eq_endpoint_of_linearIndependent_sub` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Intersection of Segments with a Common Endpoint.** Let $c, x,$ and $y$ be points in a vector space over a scalar field $\mathbb{k}$ where $0 \le 1$. If the vectors $x - c$ and $y - c$ are linearly independent over $...

### Query: `Endpoint Support`
- `Function.support` | module `Mathlib.Algebra.Notation.Support` | package Mathlib | `support` of a function is the set of points `x` such that `f x ≠ 0`.
- `SimpleGraph.Walk.endpoint_notMem_support_takeUntil` | module `Mathlib.Combinatorics.SimpleGraph.Paths` | package Mathlib | Taking a strict initial segment of a path removes the end vertex from the support.
- `AddCircle.EndpointIdent` | module `Mathlib.Topology.Instances.AddCircle.Defs` | package Mathlib | The relation identifying the endpoints of `Icc a (a + p)`.

### Query: `Pole Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `stereoInvFun_ne_north_pole` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Inverse Stereographic Projection Avoids the North Pole.** For any unit vector $v$ in a real inner product space $E$, the inverse stereographic projection from the orthogonal complement of the span of $v$ into the un...
- `EuclideanGeometry.o` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | A fixed choice of positive orientation of Euclidean space `ℝ²`

### Query: `Ring Pole Contact`
- `Ring` | module `Mathlib.Algebra.Ring.Defs` | package Mathlib | A `Ring` is a `Semiring` with negation making it an additive group.
- `stereoInvFun_ne_north_pole` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Inverse Stereographic Projection Avoids the North Pole.** For any unit vector $v$ in a real inner product space $E$, the inverse stereographic projection from the orthogonal complement of the span of $v$ into the un...
- `RingHom` | module `Mathlib.Algebra.Ring.Hom.Defs` | package Mathlib | Bundled semiring homomorphisms; use this for bundled ring homomorphisms too. This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a sensible order, even though `MonoidWithZeroHom` a...

## Grounded Mathlib/PhysLean names

- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` (PhysLean)
- `ClassicalMechanics.planeWave` (PhysLean)
- `AddCircle.EndpointIdent` (Mathlib)
- `segment_inter_eq_endpoint_of_linearIndependent_of_ne` (Mathlib)
- `segment_inter_eq_endpoint_of_linearIndependent_sub` (Mathlib)
- `Function.support` (Mathlib)
- `SimpleGraph.Walk.endpoint_notMem_support_takeUntil` (Mathlib)
- `AddCircle.EndpointIdent` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `stereoInvFun_ne_north_pole` (Mathlib)
- `EuclideanGeometry.o` (Mathlib)
- `Ring` (Mathlib)
- `stereoInvFun_ne_north_pole` (Mathlib)
- `RingHom` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0208.EndpointSupport`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.FixedFreeStringSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.HasPhysicalStringGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.IsResonantWavelength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.PoleOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.RingPoleContact`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.SatisfiesFixedFreeStandingWaveLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.StandingWaveMode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.StringEndpoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0208.WaveNumberQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
