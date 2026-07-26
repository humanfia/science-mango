# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0307.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0307.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:463e1012a801d4413afef4777e20688ba8e8d20816e2adafcf8f80cd69c4376c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `power Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `Wave Amplitude`
- `ClassicalMechanics.harmonicWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...

### Query: `Wave Power`
- `ClassicalMechanics.transverseHarmonicPlaneWave` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | Transverse monochromatic time-harmonic plane wave where the direction of propagation is taken to be `EuclideanSpace.single 2 1`. `f₀x` and `f₀y` are the respective amplitudes, `ω` is the angular frequency, `δx` and `δ...
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `ClassicalMechanics.wave_differentiable` | module `Physlib.ClassicalMechanics.WaveEquation.Basic` | package PhysLean | **Differentiability of a Plane Wave Phase.** For any direction $s$ in $d$-dimensional Euclidean space, any wave speed $c$, and any time $t$, the function mapping a position vector $x$ to the scalar value $\langle x, \...

### Query: `Wave Speed`
- `ClassicalMechanics.planeWave_waveEquation` | module `Physlib.ClassicalMechanics.WaveEquation.Basic` | package PhysLean | The plane wave satisfies the wave equation.
- `Electromagnetism.FreeSpace.c` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | The speed of light in free space.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `amplitude SIReadout`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Extensionality of Amplitude-Phase Representation.** Two amplitude-phase representations of a harmonic oscillator are equal if and only if their amplitudes and phases are respectively equal.

### Query: `power In Watts`
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `JoinedIn.joined` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | **Path Connectivity in a Subset Implies Path Connectivity.** If two points $x$ and $y$ in a topological space are joined by a path contained within a subset $F$, then they are joined by a path in the space.

### Query: `speed In Meters Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Horizontal Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `opposite Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `MulOpposite` | module `Mathlib.Algebra.Opposites` | package Mathlib | Multiplicative opposite of a type. This type inherits all additive structures on `α` and reverses left and right in multiplication.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `PowerSeries` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `ClassicalMechanics.harmonicWave` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `ClassicalMechanics.transverseHarmonicPlaneWave` (PhysLean)
- `PowerSeries` (Mathlib)
- `ClassicalMechanics.wave_differentiable` (PhysLean)
- `ClassicalMechanics.planeWave_waveEquation` (PhysLean)
- `Electromagnetism.FreeSpace.c` (PhysLean)
- `DimSpeed` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` (PhysLean)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `PowerSeries` (Mathlib)
- `JoinedIn.joined` (Mathlib)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Turing.Dir.left` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `MulOpposite` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0307.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.BoundaryReflectionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.ContinuousTravelingWave`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.EnvelopeLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.FigureArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.HasPhysicalWaveParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.MatchesProblemAndFigureData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.SatisfiesCommonMediumPowerReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.SatisfiesStandingWaveInterferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.StandingWaveEnvelopeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.WaveAmplitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.WavePower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0307.WaveSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
