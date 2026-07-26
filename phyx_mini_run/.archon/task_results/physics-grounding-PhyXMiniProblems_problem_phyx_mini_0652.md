# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0652.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0652.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a60f18bcc7062d15b048a311aab7aca64fe13bbb412b4d93a0e12e1782020629
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

### Query: `Wave Function Figure Label`
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` | module `Physlib.Electromagnetism.Vacuum.IsPlaneWave` | package PhysLean | The corresponding electric field function from `ℝ` to `EuclideanSpace ℝ (Fin d)` of a plane wave.
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | The electromagnetic potential for a Harmonic wave travelling in the `x`-direction with wave number `k`.
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PlaneWaves` | package PhysLean | **Action of the Plane Wave Functional.** For any real wave number $k$ and any Schwartz function $\psi$ from $\mathbb{R}$ to $\mathbb{C}$, the value of the plane wave functional associated with $k$ applied to $\psi$ is...

### Query: `Horizontal Tick`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_essSurj` | module `Mathlib.CategoryTheory.GuitartExact.HorizontalComposition` | package Mathlib | **Horizontal Composition of Guitart-Exact Squares.** Given two horizontally composable squares $w$ and $w'$, where the top horizontal functor of $w$ is essentially surjective and $w$ itself is Guitart-exact, the horiz...
- `Combinatorics.Line.horizontal` | module `Mathlib.Combinatorics.HalesJewett` | package Mathlib | A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`.

### Query: `Supplied Wave Function Figure`
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` | module `Physlib.Electromagnetism.Vacuum.IsPlaneWave` | package PhysLean | The corresponding electric field function from `ℝ` to `EuclideanSpace ℝ (Fin d)` of a plane wave.
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | The electromagnetic potential for a Harmonic wave travelling in the `x`-direction with wave number `k`.
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional` | module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PlaneWaves` | package PhysLean | Plane waves as a member of the dual of the Schwartz submodule of the Hilbert space. For a given `k` this corresponds to the plane wave `exp (2π I k x)`.

### Query: `Confined Particle Position Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...

### Query: `position Density Per Millimeter`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `requested Position Region`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.

### Query: `requested Position Probability`
- `FieldSpecification.statesIsPosition` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | The bool on `FieldOp` which is true only for position field operator.
- `ProbabilityTheory.Kernel` | module `Mathlib.Probability.Kernel.Defs` | package Mathlib | A kernel from a measurable space `α` to another measurable space `β` is a measurable function `κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by `MeasureTheory.Measure.instMea...
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.

### Query: `Matches Confined Particle Scenario`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `ClassicalMechanics.FreeParticle.Trajectory` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A trajectory is a time-dependent position function describing the motion of the particle in one spatial dimension. Defining the trajectory.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.TwoSquare.GuitartExact.hComp_iff_of_essSurj` (Mathlib)
- `Combinatorics.Line.horizontal` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.electricFunction` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` (PhysLean)
- `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `regionBetween` (Mathlib)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `FieldSpecification.statesIsPosition` (PhysLean)
- `ProbabilityTheory.Kernel` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `RegularExpression.matches'` (Mathlib)
- `ClassicalMechanics.FreeParticle.Trajectory` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0652.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.ConfinedParticlePositionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.HasPhysicalWaveFunctionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.HorizontalTick`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.IsUniqueMatchingDisplayedProbability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.MatchesConfinedParticleScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.MatchesDisplayedProbability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.MatchesSuppliedWaveFunctionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.SatisfiesNormalizedBornPositionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.SuppliedWaveFunctionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0652.WaveFunctionFigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
