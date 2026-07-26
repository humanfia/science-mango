# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0094.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0094.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6f4825b4d12f78f60d5178e981556b795330b0e21a0eca7b424349b7406f5532
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Irradiance Quantity`
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `irradiance In Watts Per Square Meter`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `Linearly Polarized Light`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `CKMMatrix.rows_linearly_independent` | module `Physlib.Particles.FlavorPhysics.CKMMatrix.Rows` | package PhysLean | The rows of a CKM matrix are linearly independent.
- `PauliMatrix.pauliSelfAdjoint'_linearly_independent` | module `Physlib.Relativity.PauliMatrices.SelfAdjoint` | package PhysLean | The Pauli matrices where `σi` are negated are linearly independent.

### Query: `Ideal Linear Polarizer`
- `Ideal` | module `Mathlib.RingTheory.Ideal.Defs` | package Mathlib | A (left) ideal in a semiring `R` is an additive submonoid `s` such that `a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.
- `Ideal.isLinearTopology` | module `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology` | package Mathlib | **The Adic Topology is a Linear Topology.** For any ideal $I$ of a ring $R$, the $I$-adic topology on $R$ is a linear topology.
- `QuadraticMap.polar_smul_left` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Linearity of the Polar Form in the First Argument.** For a quadratic map $Q$ on a module $M$ over a commutative ring $R$, the polar form of $Q$ is linear with respect to scalar multiplication in its first argument....

### Query: `Two Polarizer Setup`
- `QuadraticMap.polar` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | Up to a factor 2, `Q.polar` is the associated bilinear map for a quadratic map `Q`. Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
- `upperPolar_union` | module `Mathlib.Order.Concept` | package Mathlib | **Upper Polar of a Union.** For any two sets $s_1$ and $s_2$, the upper polar of their union is equal to the intersection of their individual upper polars: $upperPolar(r, s_1 \cup s_2) = upperPolar(r, s_1) \cap upperP...
- `upperPolar` | module `Mathlib.Order.Concept` | package Mathlib | The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements which `r` relates to all elements of `s`.

### Query: `radians To Degrees`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Matches Problem And Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_pow` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Regular Expression Power and Kleene Star.** For any regular expression $P$, the language matched by the $n$-th power of $P$ is equal to the $n$-th power of the language matched by $P$. Similarly, the language matche...
- `RegularExpression.matches'_map` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | The language of the map is the map of the language.

### Query: `Has Physical Parameters`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Obeys Malus Law`
- `parallelogram_law` | module `Mathlib.Analysis.InnerProductSpace.Basic` | package Mathlib | Parallelogram law
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `UnitExamples.newtonsSecondWithDim'_isDimensionallyCorrect` | module `Physlib.Units.Examples` | package PhysLean | **Dimensional Correctness of Newton's Second Law.** The formulation of Newton's Second Law, relating force to the product of mass and acceleration, is dimensionally correct; that is, the physical law is invariant unde...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `LightProfinite` (Mathlib)
- `CKMMatrix.rows_linearly_independent` (PhysLean)
- `PauliMatrix.pauliSelfAdjoint'_linearly_independent` (PhysLean)
- `Ideal` (Mathlib)
- `Ideal.isLinearTopology` (Mathlib)
- `QuadraticMap.polar_smul_left` (Mathlib)
- `QuadraticMap.polar` (Mathlib)
- `upperPolar_union` (Mathlib)
- `upperPolar` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_pow` (Mathlib)
- `RegularExpression.matches'_map` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `Dimension` (PhysLean)
- `parallelogram_law` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `UnitExamples.newtonsSecondWithDim'_isDimensionallyCorrect` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0094.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.HasRequestedIrradianceAtP`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.IdealLinearPolarizer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.IrradianceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.LinearlyPolarizedLight`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.ObeysMalusLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.SatisfiesIdealPolarizerLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0094.TwoPolarizerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
