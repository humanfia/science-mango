# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0503.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0503.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:51bb60c8e77c739b994a8778feae1ff64979ed034d26ba91f8f37e58d3997e25
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Particle Species`
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `SMCharges.toSpecies_apply_eq` | module `Physlib.Particles.StandardModel.AnomalyCancellation.Basic` | package PhysLean | **Standard Model Charge Species Component.** For any index $i \in \{0, \dots, 4\}$ and any set of charges $S$ in the Standard Model with $n$ generations, the $i$-th species of charges in $S$ is equal to the function m...
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...

### Query: `Figure Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Horizontal Tick`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_essSurj` | module `Mathlib.CategoryTheory.GuitartExact.HorizontalComposition` | package Mathlib | **Horizontal Composition of Guitart-Exact Squares.** Given two horizontally composable squares $w$ and $w'$, where the top horizontal functor of $w$ is essentially surjective and $w$ itself is Guitart-exact, the horiz...
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.

### Query: `Supplied Probability Density Figure`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf.uniformPDF_eq_pdf` | module `Mathlib.Probability.Distributions.Uniform` | package Mathlib | Check that indeed any uniform random variable has the uniformPDF.

### Query: `One Dimensional Quantum Position Setup`
- `QuantumMechanics.OneDimension.positionOperator` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | The position operator is defined as the linear map from `ℝ → ℂ` to `ℝ → ℂ` taking `ψ` to `x * ψ`.
- `FiniteDimensional` | module `Mathlib.LinearAlgebra.FiniteDimensional.Defs` | package Mathlib | `FiniteDimensional` vector spaces are defined to be finite modules. Use `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from another definition.
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic` | package PhysLean | The position in one-dimensional space associated to the configuration.

### Query: `position Density Readout`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `QuantumMechanics.positionOperator_hasDenseDomain` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | **Density of the Domain of the Position Operator.** The position operator $\mathcal{X}_i$ is a densely defined operator; that is, the subspace of the Hilbert space on which it acts is a dense subset.
- `Electromagnetism.ChargeDensity` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The charge density.

### Query: `outside Central Region`
- `IsCentralScalar` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M` on `α` are equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity for `•`.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `MeasureTheory.OuterMeasure.dirac` | module `Mathlib.MeasureTheory.OuterMeasure.Operations` | package Mathlib | The dirac outer measure.

### Query: `requested Position Event`
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `requested Position Probability`
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `ProbabilityTheory.Kernel` | module `Mathlib.Probability.Kernel.Defs` | package Mathlib | A kernel from a measurable space `α` to another measurable space `β` is a measurable function `κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by `MeasureTheory.Measure.instMea...
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `TensorSpecies.Tensor` (PhysLean)
- `SMCharges.toSpecies_apply_eq` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_essSurj` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf.uniformPDF_eq_pdf` (Mathlib)
- `QuantumMechanics.OneDimension.positionOperator` (PhysLean)
- `FiniteDimensional` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ConfigurationSpace.toSpace` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `QuantumMechanics.positionOperator_hasDenseDomain` (PhysLean)
- `Electromagnetism.ChargeDensity` (PhysLean)
- `IsCentralScalar` (Mathlib)
- `regionBetween` (Mathlib)
- `MeasureTheory.OuterMeasure.dirac` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `ProbabilityTheory.Kernel` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0503.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.HasPhysicalProbabilityDensityParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.HorizontalTick`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.IsUniqueMatchingAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.MatchesDisplayedProbability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.MatchesNeutronPositionScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.MatchesSuppliedProbabilityDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.OneDimensionalQuantumPositionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.ParticleSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.SatisfiesOneDimensionalBornRule`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0503.SuppliedProbabilityDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
