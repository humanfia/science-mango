# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0646.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0646.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:5670e950e1416557d53a3c000ec7a131b2c4fcef5e450ce77f648a1e0f6ceb9c
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `frequency Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `Filter.Frequently` | module `Mathlib.Order.Filter.Defs` | package Mathlib | `f.Frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in atTop, p x` means that there exist arbitrarily large `x` for which `p` holds true.
- `UnitExamples.cosDim_isDimensionallyCorrect` | module `Physlib.Units.Examples` | package PhysLean | **Dimensional Correctness of the Cosine of Time and Frequency.** The expression representing the cosine of the product of a time quantity and a frequency quantity is dimensionally correct, meaning it remains invariant...

### Query: `speed Dimension`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `probability Density Dimension`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `wien Displacement Constant Dimension`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `Affine.Simplex.centroid_vsub_eq` | module `Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid` | package Mathlib | The vector from any point to the centroid is the average of vectors to the simplex vertices.

### Query: `Wavelength Quantity`
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | **Inverse Square of the Characteristic Length.** For a quantum harmonic oscillator with mass $m$, angular frequency $\omega$, and characteristic length $\xi$, the square of the reciprocal of the characteristic length...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Position Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Frequency Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.cosDim_isDimensionallyCorrect` | module `Physlib.Units.Examples` | package PhysLean | **Dimensional Correctness of the Cosine of Time and Frequency.** The expression representing the cosine of the product of a time quantity and a frequency quantity is dimensionally correct, meaning it remains invariant...
- `Mathlib.Tactic.Peel.frequently_congr` | module `Mathlib.Tactic.Peel` | package Mathlib | **Congruence of the Frequently Quantifier.** Given a filter $f$ on a type $\alpha$ and two predicates $p, q: \alpha \to \text{Prop}$, if $p(x)$ is equivalent to $q(x)$ for all $x$, then $p$ holds frequently for $f$ if...

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `Probability Density Quantity`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf_def` | module `Mathlib.Probability.Density` | package Mathlib | **Definition of the Probability Density Function.** The probability density function of a random variable $X: \Omega \to E$ with respect to a probability measure $\mathbb{P}$ and a reference measure $\mu$ is defined a...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `Filter.Frequently` (Mathlib)
- `UnitExamples.cosDim_isDimensionallyCorrect` (PhysLean)
- `DimSpeed` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `LocallyConstant` (Mathlib)
- `Affine.Simplex.centroid_vsub_eq` (Mathlib)
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` (PhysLean)
- `LengthUnit` (PhysLean)
- `Dimension` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.cosDim_isDimensionallyCorrect` (PhysLean)
- `Mathlib.Tactic.Peel.frequently_congr` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf_def` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0646.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.EmitterKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.FireflyBlackbodyPeakSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.FrequencyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.HasMeasuredFireflySpectrumPeak`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.HasPhysicalPeakMatchingParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.HasSamePeakFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.MatchesFireflyBlackbodyScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.MatchesPrimaryRaster646`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.MatchesReportedFireflySpectrumCaption`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.PositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.PrimaryRaster646`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.PrimaryRasterAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.PrimaryRasterAxisRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.PrimaryRasterCurveGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.ProbabilityDensityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.ReportedFireflySpectrumCaption`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.SatisfiesVacuumDispersionAndWienLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.SpectrumAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.SpectrumAxisRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.UsesStandardBlackbodyConstants`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.WavelengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0646.WienDisplacementConstantQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
