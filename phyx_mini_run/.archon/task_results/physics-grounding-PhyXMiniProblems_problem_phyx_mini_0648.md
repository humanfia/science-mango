# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0648.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0648.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:af811b953555f82da99506da6212eaa2621ff20b203e5c899162110bbbf548e3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Quantum Particle Kind`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `ClassicalMechanics.FreeParticle.Trajectory` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A trajectory is a time-dependent position function describing the motion of the particle in one spatial dimension. Defining the trajectory.
- `ClassicalMechanics.FreeParticle.velocity` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | The velocity of a trajectory at a given time. This is defined as the time derivative of the position function.

### Query: `Wave Function Curve Shape`
- `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Eigenfunction` | package PhysLean | The `n`th eigenfunction of the Harmonic oscillator is defined as the function `ℝ → ℂ` taking `x : ℝ` to `1/√(2^n n!) 1/√(√π ξ) * physHermite n (x / ξ) * e ^ (- x²/ (2 ξ²))`.
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.magneticFunction` | module `Physlib.Electromagnetism.Vacuum.IsPlaneWave` | package PhysLean | The corresponding magnetic field function from `ℝ` to `Fin d × Fin d → ℝ` of a plane wave.
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PlaneWaves` | package PhysLean | **Action of the Plane Wave Functional.** For any real wave number $k$ and any Schwartz function $\psi$ from $\mathbb{R}$ to $\mathbb{C}$, the value of the plane wave functional associated with $k$ applied to $\psi$ is...

### Query: `Neutron Wave Function Figure`
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` | module `Physlib.Electromagnetism.Vacuum.IsPlaneWave` | package PhysLean | The corresponding electric field function from `ℝ` to `EuclideanSpace ℝ (Fin d)` of a plane wave.
- `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Eigenfunction` | package PhysLean | The `n`th eigenfunction of the Harmonic oscillator is defined as the function `ℝ → ℂ` taking `x : ℝ` to `1/√(2^n n!) 1/√(√π ξ) * physHermite n (x / ξ) * e ^ (- x²/ (2 ξ²))`.
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PlaneWaves` | package PhysLean | **Action of the Plane Wave Functional.** For any real wave number $k$ and any Schwartz function $\psi$ from $\mathbb{R}$ to $\mathbb{C}$, the value of the plane wave functional associated with $k$ applied to $\psi$ is...

### Query: `Neutron Position Experiment`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Satisfies One Dimensional Position Quantum Laws`
- `QuantumMechanics.OneDimension.positionOperator` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | The position operator is defined as the linear map from `ℝ → ℂ` to `ℝ → ℂ` taking `ψ` to `x * ψ`.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace_apply` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic` | package PhysLean | The physical-space coordinate associated to a configuration is its chosen global coordinate.

### Query: `Matches Problem Statement And Figure`
- `LibraryNote.continuity_lemma_statement` | module `Mathlib.Topology.Continuous` | package Mathlib | The library contains many lemmas stating that functions/operations are continuous. There are many ways to formulate the continuity of operations. Some are more convenient than others. Note: for the most part this note...
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Position Interval Readout`
- `toIcoMod` | module `Mathlib.Algebra.Order.ToIntervalMod` | package Mathlib | Reduce `b` to the interval `Ico a (a + p)`.
- `toIcoDiv` | module `Mathlib.Algebra.Order.ToIntervalMod` | package Mathlib | The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ico a (a + p)`.
- `toIcoMod_sub_self_eq_mul` | module `Mathlib.Algebra.Order.ToIntervalMod` | package Mathlib | **Difference between the Interval Reduction and the Original Value.** For a given period $p > 0$ and a starting point $a$, the difference between the reduction of $b$ to the interval $[a, a + p)$ and the original valu...

### Query: `region`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `interval Probability`
- `IntervalIntegrable` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these intervals is always empty, so this...
- `ProbabilityTheory.integral_truncation_eq_intervalIntegral` | module `Mathlib.Probability.StrongLaw` | package Mathlib | **Integral of a Truncated Function.** Let $f$ be an almost everywhere strongly measurable real-valued function with respect to a measure $\mu$. For any non-negative real number $A$, the integral of the truncation of $...
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `ClassicalMechanics.FreeParticle.Trajectory` (PhysLean)
- `ClassicalMechanics.FreeParticle.velocity` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.magneticFunction` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `QuantumMechanics.OneDimension.positionOperator` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace_apply` (PhysLean)
- `LibraryNote.continuity_lemma_statement` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `toIcoMod` (Mathlib)
- `toIcoDiv` (Mathlib)
- `toIcoMod_sub_self_eq_mul` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `IntervalIntegrable` (Mathlib)
- `ProbabilityTheory.integral_truncation_eq_intervalIntegral` (Mathlib)
- `intervalIntegral` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0648.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.MatchesProblemStatementAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.NeutronPositionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.NeutronWaveFunctionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.PositionIntervalReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.QuantumParticleKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.SatisfiesOneDimensionalPositionQuantumLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0648.WaveFunctionCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
