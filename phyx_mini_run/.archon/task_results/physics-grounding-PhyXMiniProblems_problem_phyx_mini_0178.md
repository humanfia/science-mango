# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0178.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0178.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b5e55382617e63ae79d1a0721757c19d198b08d8598ffa61c7734212a82c1df8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | The characteristic length `ξ` of the harmonic oscillator is defined as `√(ℏ /(m ω))`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `String State`
- `Turing.TM1to1.Λ'.write` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Write State Constructor.** A state in the modified Turing machine configuration that represents the instruction to write a specific symbol from the alphabet $\Gamma$ to the tape, followed by the execution of a given...
- `CongrState` | module `Mathlib.Tactic.CongrExclamation` | package Mathlib | **Congruence Tactic State.** A structure representing the state of a congruence-based decomposition process, consisting of a collection of unresolved goals (metavariables) that the procedure could not automatically di...
- `Turing.TM0to1.Λ'.act` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Action State Constructor.** An action state is defined as a state in the emulating machine that represents the intermediate process of executing a specific Turing machine statement and then transitioning to a given...

### Query: `String Endpoint`
- `AddCircle.EndpointIdent` | module `Mathlib.Topology.Instances.AddCircle.Defs` | package Mathlib | The relation identifying the endpoints of `Icc a (a + p)`.
- `segment_inter_eq_endpoint_of_linearIndependent_of_ne` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Intersection of Segments with a Common Endpoint and Linearly Independent Directions.** Let $E$ be a module over an ordered domain $\mathbb{k}$. Suppose $x, y \in E$ are linearly independent. For any $c \in E$ and di...
- `segment_inter_eq_endpoint_of_linearIndependent_sub` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Intersection of Segments with a Common Endpoint.** Let $c, x,$ and $y$ be points in a vector space over a scalar field $\mathbb{k}$ where $0 \le 1$. If the vectors $x - c$ and $y - c$ are linearly independent over $...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `Dim Frequency`
- `Filter.Frequently` | module `Mathlib.Order.Filter.Defs` | package Mathlib | `f.Frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in atTop, p x` means that there exist arbitrarily large `x` for which `p` holds true.
- `UnitExamples.cosDim_isDimensionallyCorrect` | module `Physlib.Units.Examples` | package PhysLean | **Dimensional Correctness of the Cosine of Time and Frequency.** The expression representing the cosine of the product of a time quantity and a frequency quantity is dimensionally correct, meaning it remains invariant...
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.

### Query: `Dim Tension`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `WithDim` | module `Physlib.Units.WithDim.Basic` | package PhysLean | The type `M` carrying an instance of a dimension `d`.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.

### Query: `Dim Linear Mass Density`
- `FluidDynamics.MassDensity` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A mass density field on `d`-dimensional space.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.

### Query: `si Readout`
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI_charge` | module `Physlib.Units.Basic` | package PhysLean | **SI Charge Unit.** In the International System of Units (SI), the fundamental unit of electric charge is defined to be the coulomb.

## Grounded Mathlib/PhysLean names

- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Turing.TM1to1.Λ'.write` (Mathlib)
- `CongrState` (Mathlib)
- `Turing.TM0to1.Λ'.act` (Mathlib)
- `AddCircle.EndpointIdent` (Mathlib)
- `segment_inter_eq_endpoint_of_linearIndependent_of_ne` (Mathlib)
- `segment_inter_eq_endpoint_of_linearIndependent_sub` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `Filter.Frequently` (Mathlib)
- `UnitExamples.cosDim_isDimensionallyCorrect` (PhysLean)
- `dimH` (Mathlib)
- `dimH` (Mathlib)
- `WithDim` (PhysLean)
- `dim` (PhysLean)
- `FluidDynamics.MassDensity` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `UnitChoices.SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI_charge` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0178.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.DimFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.DimLinearMassDensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.DimTension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.HasPositivePhysicalData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.IsRequiredFourAntinodeMode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.MatchesInitialFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.ObeysFixedEndStandingWaveLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.ObeysTransverseStringWaveSpeedLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.StringEndpoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.StringState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.TensionIncreasedByFour`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0178.VibratingStringSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
