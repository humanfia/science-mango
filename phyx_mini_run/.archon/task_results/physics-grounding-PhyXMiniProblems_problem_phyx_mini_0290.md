# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0290.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0290.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:43b1b145373e4dbd9032372c67a7f61ffe749949bba55ea4b4b5360813ff9694
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `Polynomial.derivative` | module `Mathlib.Algebra.Polynomial.Derivative` | package Mathlib | `derivative p` is the formal derivative of the polynomial `p`
- `bernsteinPolynomial.iterate_derivative_at_1` | module `Mathlib.RingTheory.Polynomial.Bernstein` | package Mathlib | **The $(n-\nu)$-th Derivative of a Bernstein Polynomial at 1.** For a commutative ring $R$ and natural numbers $\nu \leq n$, the $(n-\nu)$-th iterative derivative of the Bernstein polynomial $B_{\nu, n}(X)$ evaluated...
- `derivWithin_zero_of_not_accPt` | module `Mathlib.Analysis.Calculus.Deriv.Basic` | package Mathlib | **Derivative at an Isolated Point.** If a point $x$ is not an accumulation point of a set $s$, then the derivative of any function $f$ within $s$ at $x$ is zero.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Amplitude Quantity`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Extensionality of Amplitude-Phase Representation.** Two amplitude-phase representations of a harmonic oscillator are equal if and only if their amplitudes and phases are respectively equal.

### Query: `Wavelength Quantity`
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | **Inverse Square of the Characteristic Length.** For a quantum harmonic oscillator with mass $m$, angular frequency $\omega$, and characteristic length $\xi$, the square of the reciprocal of the characteristic length...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Signed Length Quantity`
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Duration Quantity`
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.
- `Dimension.L𝓭_time` | module `Physlib.Units.Dimension` | package PhysLean | **Time Component of the Length Dimension.** The time component of the length dimension is equal to zero.
- `Dimensionful.ext` | module `Physlib.Units.Basic` | package PhysLean | **Extensionality of Dimensionful Quantities.** Two dimensionful quantities associated with a type that carries a dimension are equal if their underlying values are equal.

### Query: `Angular Frequency Quantity`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Wave Number Quantity`
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone.
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Exponential Property of the Quanta Wave Number.** For any site index $n \in \{0, \dots, N-1\}$ and any quanta wave number $k$, the complex exponential of $i \cdot k \cdot (n+1) \cdot a$ is equal to the product of th...
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Quantized Wave Number Periodic Identity.** For any natural number $n$ and any quantized wave number $k$ associated with a tight-binding chain of $N$ sites and lattice constant $a$, the complex exponential $\exp(i k...

### Query: `Transverse Velocity Quantity`
- `GalileanGroup.ofSpaceTranslation_velocity` | module `Physlib.SpaceAndTime.GalileanGroup.Basic` | package PhysLean | **Velocity of a Pure Spatial Translation.** For any vector $a$ in $d$-dimensional Euclidean space, the velocity (or boost) component of the Galilean transformation representing a pure spatial translation by $a$ is zero.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `transverseTactics` | module `Physlib.Meta.TransverseTactics` | package PhysLean | Applies `visitTacticInfo` to each tactic in a file.

## Grounded Mathlib/PhysLean names

- `Polynomial.derivative` (Mathlib)
- `bernsteinPolynomial.iterate_derivative_at_1` (Mathlib)
- `derivWithin_zero_of_not_accPt` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` (PhysLean)
- `LengthUnit` (PhysLean)
- `Dimension` (PhysLean)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist` (Mathlib)
- `LengthUnit` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `Dimension.L𝓭_time` (PhysLean)
- `Dimensionful.ext` (PhysLean)
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` (PhysLean)
- `GalileanGroup.ofSpaceTranslation_velocity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `transverseTactics` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0290.AmplitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.AngularFrequencyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.AxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.DisplacementTimeGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.DurationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.GraphAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.HasPhysicalTravelingWaveParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.MatchesDisplayedVelocity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.MatchesPrimaryWaveGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.MatchesStringWaveProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.PropagationDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.SatisfiesSinusoidalTravelingWaveLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.SignedLengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.StringWaveKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.TransverseVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.TravelingStringWaveSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.WaveGraphLandmark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.WaveNumberQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0290.WavelengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
