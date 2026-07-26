# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0653.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0653.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7021b9c696e51a08db27b24f419c653e7703c68cdb8259bd437e06e6af0e3fc1
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

### Query: `Probability Density Quantity`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf_def` | module `Mathlib.Probability.Density` | package Mathlib | **Definition of the Probability Density Function.** The probability density function of a random variable $X: \Omega \to E$ with respect to a probability measure $\mathbb{P}$ and a reference measure $\mu$ is defined a...

### Query: `position Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `density Readout`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `jacobson_density` | module `Mathlib.RingTheory.SimpleModule.Basic` | package Mathlib | **Jacobson Density Theorem.** Let $M$ be a module over a ring $R$. For any endomorphism $f$ of $M$ that commutes with all $R$-linear endomorphisms of $M$ (i.e., $f \in \text{End}_{\text{End}_R(M)}(M)$) and for any fin...
- `schnirelmannDensity` | module `Mathlib.Combinatorics.Schnirelmann` | package Mathlib | The Schnirelmann density is defined as the infimum of $|A ∩ {1, ..., n}| / n$ as n ranges over the positive naturals.

### Query: `position From Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `Matrix.fromBlocks` | module `Mathlib.Data.Matrix.Block` | package Mathlib | We can form a single large matrix by flattening smaller 'block' matrices of compatible dimensions.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `One Dimensional Position Distribution`
- `FiniteDimensional` | module `Mathlib.LinearAlgebra.FiniteDimensional.Defs` | package Mathlib | `FiniteDimensional` vector spaces are defined to be finite modules. Use `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from another definition.
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic` | package PhysLean | The position in one-dimensional space associated to the configuration.
- `QuantumMechanics.OneDimension.HilbertSpace.positionState` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PositionStates` | package PhysLean | Position state as a member of the dual of the Schwartz submodule of the Hilbert space.

### Query: `density At Centimeter Coordinate`
- `LipschitzWith.coordinate` | module `Mathlib.Analysis.Normed.Lp.lpSpace` | package Mathlib | **Lipschitz Continuity of Functions into $L^\infty$.** A function $f$ from a pseudometric space into the space of bounded sequences $\ell^\infty(\iota, \mathbb{R})$ is Lipschitz continuous with constant $K$ if and onl...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `Density Curve Shape`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `jacobson_density` | module `Mathlib.RingTheory.SimpleModule.Basic` | package Mathlib | **Jacobson Density Theorem.** Let $M$ be a module over a ring $R$. For any endomorphism $f$ of $M$ that commutes with all $R$-linear endomorphisms of $M$ (i.e., $f \in \text{End}_{\text{End}_R(M)}(M)$) and for any fin...
- `schnirelmannDensity` | module `Mathlib.Combinatorics.Schnirelmann` | package Mathlib | The Schnirelmann density is defined as the infimum of $|A ∩ {1, ..., n}| / n$ as n ranges over the positive naturals.

### Query: `Horizontal Tick Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the horizontal identity 2-square.
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf_def` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `jacobson_density` (Mathlib)
- `schnirelmannDensity` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `Matrix.fromBlocks` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `FiniteDimensional` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.positionState` (PhysLean)
- `LipschitzWith.coordinate` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `jacobson_density` (Mathlib)
- `schnirelmannDensity` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ₕ»` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0653.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.DensityCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.FigurePlotsTriangularPositionDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.HorizontalTickLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.IsCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.IsMostLikelyCoordinateCm`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.IsUniqueCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.IsUniqueMostLikelyCoordinateCm`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.MatchesSuppliedPositionDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.OneDimensionalPositionDistribution`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.ParticlePositionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.PositionDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.PositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.ProbabilityDensityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0653.SatisfiesPositionProbabilityLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
