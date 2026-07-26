# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0502.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0502.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d24620fbf6f45cd7c56e70e78ef3f8bb7a26ab324a9a1ba14e08893a4157d4b6
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Quantum Particle Kind`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `ClassicalMechanics.FreeParticle.Trajectory` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A trajectory is a time-dependent position function describing the motion of the particle in one spatial dimension. Defining the trajectory.
- `ClassicalMechanics.FreeParticle.velocity` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | The velocity of a trajectory at a given time. This is defined as the time derivative of the position function.

### Query: `Density Peak Label`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `tendsto_integral_peak_smul_of_integrable_of_tendsto` | module `Mathlib.MeasureTheory.Integral.PeakFunction` | package Mathlib | If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and has a limit `a` at `x₀`,...
- `integrableOn_peak_smul_of_integrableOn_of_tendsto` | module `Mathlib.MeasureTheory.Integral.PeakFunction` | package Mathlib | If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and `g` is integrable and has a limit at `x₀`, then `φᵢ • g` is eventually integrable.

### Query: `Probability Density Curve Shape`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `ProbabilityTheory.betaPDFReal` | module `Mathlib.Probability.Distributions.Beta` | package Mathlib | The probability density function of the beta distribution with shape parameters `α` and `β`. Returns `(1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)` when `0 < x < 1` and `0` otherwise.

### Query: `Probability Density Figure`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf_def` | module `Mathlib.Probability.Density` | package Mathlib | **Definition of the Probability Density Function.** The probability density function of a random variable $X: \Omega \to E$ with respect to a probability measure $\mathbb{P}$ and a reference measure $\mu$ is defined a...

### Query: `Electron Position Experiment`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.OneDimension.positionOperatorSchwartz_apply` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | **Action of the Position Operator on Schwartz Functions.** For any Schwartz function $\psi \in \mathcal{S}(\mathbb{R}, \mathbb{C})$ and any real number $x$, the value of the position operator applied to $\psi$ at $x$...

### Query: `Satisfies Born Position Density Law`
- `Born` | module `Mathlib.Topology.Category.Born` | package Mathlib | The category of bornologies.
- `FirstOrder.Language.realize_denselyOrdered` | module `Mathlib.ModelTheory.Order` | package Mathlib | **Satisfaction of the Density Sentence.** If a first-order structure $M$ is a densely ordered set, then the first-order sentence expressing the density of an order is satisfied by $M$.
- `Born.instInhabited` | module `Mathlib.Topology.Category.Born` | package Mathlib | **Inhabitedness of the Category of Bornologies.** The type of all bornological spaces is inhabited, as it contains at least one element, specifically the bornology defined on the singleton set.

### Query: `Matches Problem Statement And Figure`
- `LibraryNote.continuity_lemma_statement` | module `Mathlib.Topology.Continuous` | package Mathlib | The library contains many lemmas stating that functions/operations are continuous. There are many ways to formulate the continuity of operations. Some are more convenient than others. Note: for the most part this note...
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Detection Strip Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PhragmenLindelof.horizontal_strip` | module `Mathlib.Analysis.Complex.PhragmenLindelof` | package Mathlib | **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`. Let `f : ℂ → E` be a function such that * `f` is differentiable on `U` and is continuous on its closure; * `‖f z‖` is bounded from above by `A *...
- `PhragmenLindelof.vertical_strip` | module `Mathlib.Analysis.Complex.PhragmenLindelof` | package Mathlib | **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < re z < b}`. Let `f : ℂ → E` be a function such that * `f` is differentiable on `U` and is continuous on its closure; * `‖f z‖` is bounded from above by `A *...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `ClassicalMechanics.FreeParticle.Trajectory` (PhysLean)
- `ClassicalMechanics.FreeParticle.velocity` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `tendsto_integral_peak_smul_of_integrable_of_tendsto` (Mathlib)
- `integrableOn_peak_smul_of_integrableOn_of_tendsto` (Mathlib)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `ProbabilityTheory.betaPDFReal` (Mathlib)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf_def` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.OneDimension.positionOperatorSchwartz_apply` (PhysLean)
- `Born` (Mathlib)
- `FirstOrder.Language.realize_denselyOrdered` (Mathlib)
- `Born.instInhabited` (Mathlib)
- `LibraryNote.continuity_lemma_statement` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PhragmenLindelof.horizontal_strip` (Mathlib)
- `PhragmenLindelof.vertical_strip` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0502.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.DensityPeakLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.DetectionStripReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.ElectronPositionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.MatchesProblemStatementAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.ProbabilityDensityCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.ProbabilityDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.QuantumParticleKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.SatisfiesBornPositionDensityLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0502.UsesNarrowStripProbabilityApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
