# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0550.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0550.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f5115044e0f1990e13e14fff8fe0240234b26359c93cadbe437fcc3298301003
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Position Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Wave Amplitude Quantity`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Recover amplitude–phase data from standard initial conditions, as the polar coordinates of the phase vector `(x₀, v₀ / ω)` embedded as `z = x₀ + (v₀ / ω) i`: the amplitude is `‖z‖` and the phase is `Complex.arg z`. Se...

### Query: `Quadratic Coefficient Quantity`
- `QuadraticAlgebra` | module `Mathlib.Algebra.QuadraticAlgebra.Defs` | package Mathlib | Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to `R[X]/(X^2-b*X-a)`.
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `SMRHN.PlusU1.ElevenPlane.quadCoeff` | module `Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.PlaneNonSols` | package PhysLean | The coefficients of the quadratic equation in our basis.

### Query: `position Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `position From Readout`
- `Turing.PartrecToTM2.Λ'.read` | module `Mathlib.Computability.TuringMachine.ToPartrec` | package Mathlib | **Tape Read Operation.** A program instruction that reads the current symbol from the tape (represented as an optional value from the alphabet $\Gamma'$) and transitions to a subsequent program position determined by...
- `Matrix.fromBlocks` | module `Mathlib.Data.Matrix.Block` | package Mathlib | We can form a single large matrix by flattening smaller 'block' matrices of compatible dimensions.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `wave Amplitude Readout`
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Initial conditions for the harmonic oscillator specified by an amplitude `A` and a phase offset `φ`, describing the solution `x(t) = A cos (ω t - φ)`. The conditions can be converted to the standard `InitialConditions...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Solution` | package PhysLean | Recover amplitude–phase data from standard initial conditions, as the polar coordinates of the phase vector `(x₀, v₀ / ω)` embedded as `z = x₀ + (v₀ / ω) i`: the amplitude is `‖z‖` and the phase is `Complex.arg z`. Se...

### Query: `coefficient Readout`
- `Polynomial.coeff` | module `Mathlib.Algebra.Polynomial.Basic` | package Mathlib | `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`.
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `FTheory.SU5.FiveQuanta.anomalyCoefficient` | module `Physlib.StringTheory.FTheory.SU5.Quanta.FiveQuanta` | package PhysLean | The anomaly coefficient of a `FiveQuanta` is given by the pair of integers: `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`. The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084. The second component is for t...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions` (PhysLean)
- `QuadraticAlgebra` (Mathlib)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `SMRHN.PlusU1.ElevenPlane.quadCoeff` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `Turing.PartrecToTM2.Λ'.read` (Mathlib)
- `Matrix.fromBlocks` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions` (PhysLean)
- `Polynomial.coeff` (Mathlib)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `FTheory.SU5.FiveQuanta.anomalyCoefficient` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0550.HasQuadraticWaveProfile`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.IsNormalizedInsideBox`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.IsSquareIntegrablePositionState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.MatchesSuppliedParticleInBoxFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.OneDimensionalPositionState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.ParticleInBoxFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.ParticleInBoxSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.PositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.QuadraticCoefficientQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.SatisfiesImpenetrableWallBoundaryCondition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.SatisfiesPositionBornRule`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.WallRendering`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0550.WaveAmplitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
