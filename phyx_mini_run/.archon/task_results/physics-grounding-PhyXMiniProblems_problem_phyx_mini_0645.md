# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0645.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0645.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:0231e62334aa1ca1b9877b5123691bf0d3b9b6f81845b18dc2036b818ceba4ea
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

### Query: `Probability Density Quantity`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf_def` | module `Mathlib.Probability.Density` | package Mathlib | **Definition of the Probability Density Function.** The probability density function of a random variable $X: \Omega \to E$ with respect to a probability measure $\mathbb{P}$ and a reference measure $\mu$ is defined a...

### Query: `position Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `density Readout`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `jacobson_density` | module `Mathlib.RingTheory.SimpleModule.Basic` | package Mathlib | **Jacobson Density Theorem.** Let $M$ be a module over a ring $R$. For any endomorphism $f$ of $M$ that commutes with all $R$-linear endomorphisms of $M$ (i.e., $f \in \text{End}_{\text{End}_R(M)}(M)$) and for any fin...
- `schnirelmannDensity` | module `Mathlib.Combinatorics.Schnirelmann` | package Mathlib | The Schnirelmann density is defined as the infimum of $|A ∩ {1, ..., n}| / n$ as n ranges over the positive naturals.

### Query: `position From Millimeters`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).

### Query: `Electron Position State`
- `QuantumMechanics.OneDimension.HilbertSpace.positionState_apply` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PositionStates` | package PhysLean | **Evaluation of the Position State.** For any real number $x$ and any Schwartz function $\psi$ in $\mathcal{S}(\mathbb{R}, \mathbb{C})$, the position state at $x$ applied to $\psi$ is equal to the value of the functio...
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `QuantumMechanics.OneDimension.positionStates_generalized_eigenvector_positionOperatorUnbounded` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | **Generalized Eigenvectors of the Position Operator.** For any real number $x$, the position state $\delta_x$ is a generalized eigenvector of the unbounded position operator with eigenvalue $x$.

### Query: `density At Millimeter Coordinate`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

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
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf_def` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `QuantumMechanics.positionCLM` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `jacobson_density` (Mathlib)
- `schnirelmannDensity` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.positionState_apply` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `QuantumMechanics.OneDimension.positionStates_generalized_eigenvector_positionOperatorUnbounded` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0645.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.DensityCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.ElectronPositionState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.ElectronStripExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.FigurePlotsTriangularPositionDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.IsUniqueClosestDisplayedCount`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.MatchesElectronExperimentScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.MatchesSuppliedPositionDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.ParticleSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.PositionDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.PositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.ProbabilityDensityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.SatisfiesExpectedStripCountLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0645.SatisfiesPositionProbabilityLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
