# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0313.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0313.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a7ea8e4ea6d10c84792247496c97e3f9a4bfc2c84ba6f25106a2af14ecc0cdae
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

### Query: `Signed Length Quantity`
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Acoustic Displacement Amplitude`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `signed Length Readout`
- `signedDist` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | The signed distance between two points `p` and `q`, in the direction of a reference vector `v`. It is the size of `q - p` in the direction of `v`. In the degenerate case `v = 0`, it returns `0`. TODO: once we have a t...
- `MeasureTheory.SignedMeasure` | module `Mathlib.MeasureTheory.VectorMeasure.Basic` | package Mathlib | A `SignedMeasure` is an `ℝ`-vector measure.
- `signedDist_neg` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Negation of the Reference Vector in Signed Distance.** The signed distance from a point $p$ to a point $q$ with respect to the negation of a reference vector $v$ is equal to the negative of the signed distance from...

### Query: `amplitude Readout`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Extensionality of Amplitude-Phase Representation.** Two amplitude-phase representations of a harmonic oscillator are equal if and only if their amplitudes and phases are respectively equal.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext_iff` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | **Equality of Harmonic Oscillator Amplitude-Phase Representations.** Two amplitude-phase representations of a harmonic oscillator are equal if and only if their amplitudes and phases are respectively equal.

### Query: `Source Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.

### Query: `Radiation Pattern`
- `SymbolicDynamics.FullShift.Pattern` | module `Mathlib.Dynamics.SymbolicDynamics.Basic` | package Mathlib | A *pattern* is a finite configuration in the full shift `A^G`. It consists of: * a full configuration `config : G → A` in the full shift; * a finite subset `support : Finset G` of coordinates, called the support of `p...
- `SymbolicDynamics.FullShift.Pattern.fromConfig` | module `Mathlib.Dynamics.SymbolicDynamics.Basic` | package Mathlib | Extract the finite pattern given by restricting a configuration `x : G → A` to a finite subset `U : Finset G`. The pattern has `config g = x g` for `g ∈ U` and `config g = default` outside `U`, with support `U`. In ot...
- `QuantumMechanics.radiusRegPowCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`.

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
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist` (Mathlib)
- `LengthUnit` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.displacement` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `signedDist` (Mathlib)
- `MeasureTheory.SignedMeasure` (Mathlib)
- `signedDist_neg` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.ext_iff` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `SymbolicDynamics.FullShift.Pattern` (Mathlib)
- `SymbolicDynamics.FullShift.Pattern.fromConfig` (Mathlib)
- `QuantumMechanics.radiusRegPowCLM` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0313.AcousticDisplacementAmplitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.FourSourceSoundSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.HasIdenticalCoherentPointSources`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.IsUniqueMatchingDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.MatchesDisplayedAmplitudeChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.MatchesFourSourceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.PointSoundSource`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.RadiationPattern`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SatisfiesCoherentPhasorSuperposition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SatisfiesCollinearRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SatisfiesMonochromaticPropagation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SatisfiesNegligibleAttenuation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SignedLengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0313.SpacingEqualsWavelength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
