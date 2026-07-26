# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0505.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0505.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:21bd2374bd857a511e234c98dfbafa0419f282d9a9d7f97ff8826cad0b8dadba
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `position Axis Unit`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `Dimension.one_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length of the Unit Dimension.** The length component of the unit dimension is zero.

### Query: `probability Density Dimension`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Electron Position Experiment`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.OneDimension.positionOperatorSchwartz_apply` | module `Physlib.QuantumMechanics.Operators.OneDimension.Position` | package PhysLean | **Action of the Position Operator on Schwartz Functions.** For any Schwartz function $\psi \in \mathcal{S}(\mathbb{R}, \mathbb{C})$ and any real number $x$, the value of the position operator applied to $\psi$ at $x$...

### Query: `Probability Density Figure Axes`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `ProbabilityTheory.Kernel.densityProcess` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | An `ℕ`-indexed martingale that is a density for `κ` with respect to `ν` on the sets in `countablePartition γ n`. Used to define its limit `ProbabilityTheory.Kernel.density`, which is a density for those kernels for al...

### Query: `Detection Question Readout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...
- `HahnSeries.order_lt_iff_exists` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Characterization of the Order of a Hahn Series.** For a non-zero Hahn series $x$ and an element $i$ in the index set $\Gamma$, the order of $x$ is strictly less than $i$ if and only if there exists some $j < i$ such...

### Query: `Matches Supplied Probability Density Figure`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `MeasureTheory.pdf.uniformPDF_eq_pdf` | module `Mathlib.Probability.Distributions.Uniform` | package Mathlib | Check that indeed any uniform random variable has the uniformPDF.

### Query: `Matches Detection Question`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_pow` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Regular Expression Power and Kleene Star.** For any regular expression $P$, the language matched by the $n$-th power of $P$ is equal to the $n$-th power of the language matched by $P$. Similarly, the language matche...
- `RegularExpression.matches'_mul` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Concatenation of Regular Expressions.** The language associated with the concatenation of two regular expressions $P$ and $Q$ is equal to the concatenation of the languages associated with $P$ and $Q...

### Query: `Satisfies Born And Counting Laws`
- `Born` | module `Mathlib.Topology.Category.Born` | package Mathlib | The category of bornologies.
- `Nat.count` | module `Mathlib.Data.Nat.Count` | package Mathlib | Count the number of naturals `k < n` satisfying `p k`.
- `Nat.count_succ_eq_succ_count_iff` | module `Mathlib.Data.Nat.Count` | package Mathlib | **Incrementing the Count of Satisfying Natural Numbers.** For a decidable predicate $p$ and a natural number $n$, the number of integers $k$ in the range $0 \le k < n + 1$ that satisfy $p$ is equal to one more than th...

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `IsUnit` (Mathlib)
- `Dimension.one_length` (PhysLean)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.OneDimension.positionOperatorSchwartz_apply` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `ProbabilityTheory.Kernel.densityProcess` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `HahnSeries.order_lt_iff_exists` (Mathlib)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `MeasureTheory.pdf.uniformPDF_eq_pdf` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_pow` (Mathlib)
- `RegularExpression.matches'_mul` (Mathlib)
- `Born` (Mathlib)
- `Nat.count` (Mathlib)
- `Nat.count_succ_eq_succ_count_iff` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0505.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.DetectionQuestionReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.ElectronPositionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.MatchesDetectionQuestion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.MatchesSuppliedProbabilityDensityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.ProbabilityDensityFigureAxes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0505.SatisfiesBornAndCountingLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
