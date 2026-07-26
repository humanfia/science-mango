# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0518.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0518.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c8ec412336908d1ddbb37d0620530ae5b57a805e26187acda42e91b1b6c55df0
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `Searsium Energy Level`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `BoundingSieve.one_le_y` | module `Mathlib.NumberTheory.SelbergSieve` | package Mathlib | **Lower Bound on Selberg Sieve Level.** For any Selberg sieve, its level is greater than or equal to 1.
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `principal Quantum Number`
- `Filter.principal` | module `Mathlib.Order.Filter.Defs` | package Mathlib | The principal filter of `s` is the collection of all supersets of `s`.
- `NumberField.AdeleRing.principalSubgroup` | module `Mathlib.NumberTheory.NumberField.AdeleRing` | package Mathlib | The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`.
- `Nat.nth_prime_zero_eq_two` | module `Mathlib.Data.Nat.Prime.Nth` | package Mathlib | **The First Prime Number.** The $0$-indexed $n$-th prime number is $2$.

### Query: `Searsium Transition`
- `StateTransition.Respects` | module `Mathlib.Computability.StateTransition` | package Mathlib | Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions `f₁ : σ₁ → Option σ₁` and `f₂ : σ₂ → Option σ₂`, `Respects f₁ f₂ tr` means that if `tr a₁ a₂` holds initially and `f₁` takes...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `StateTransition.Reaches₁` | module `Mathlib.Computability.StateTransition` | package Mathlib | The transitive closure of a state transition function. `Reaches₁ f a b` means there is a nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`. This relation does not permit zero...

### Query: `transition Initial Level`
- `StateTransition.Reaches₁` | module `Mathlib.Computability.StateTransition` | package Mathlib | The transitive closure of a state transition function. `Reaches₁ f a b` means there is a nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`. This relation does not permit zero...
- `Real.smoothTransition` | module `Mathlib.Analysis.SpecialFunctions.SmoothTransition` | package Mathlib | An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`, `f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`.
- `StateTransition.FRespects` | module `Mathlib.Computability.StateTransition` | package Mathlib | A simpler version of `Respects` when the state transition relation `tr` is a function.

### Query: `transition Final Level`
- `Mathlib.Meta.FunProp.withIncreasedTransitionDepth` | module `Mathlib.Tactic.FunProp.Types` | package Mathlib | Increase transition depth. Return `none` if maximum transition depth has been reached.
- `Real.smoothTransition` | module `Mathlib.Analysis.SpecialFunctions.SmoothTransition` | package Mathlib | An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`, `f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`.
- `StateTransition.FRespects` | module `Mathlib.Computability.StateTransition` | package Mathlib | A simpler version of `Respects` when the state transition relation `tr` is a function.

### Query: `Searsium Photon`
- `Polynomial.mem_lifts` | module `Mathlib.Algebra.Polynomial.Lifts` | package Mathlib | **Membership in the Polynomial Lifting Subsemiring.** Let $f: R \to S$ be a semiring homomorphism. A polynomial $p \in S[X]$ belongs to the subsemiring of lifts of $f$ if and only if there exists a polynomial $q \in R...
- `RingHom.star_apply` | module `Mathlib.Algebra.Star.Basic` | package Mathlib | **Evaluation of a Star-Ring Homomorphism.** For a semiring homomorphism $f$ between a non-associative semiring $S$ and a star-ring $R$, the value of the star of $f$ applied to an element $s \in S$ is equal to the star...
- `ωCPO.omegaCompletePartialOrderEqualizer` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **$\omega$-Complete Partial Order on Equalizers.** Given two $\omega$-complete partial orders $\alpha$ and $\beta$ and two continuous functions $f, g: \alpha \to \beta$, the equalizer $\{ a \in \alpha \mid f(a) = g(a)...

### Query: `photon Energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Finpartition.coe_energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | **Energy of a Partition.** For a simple graph $G$ and a finite partition $\mathcal{P}$ of its vertex set, the energy of $\mathcal{P}$ (viewed as an element of a strictly ordered field) is equal to the sum of the squar...

### Query: `Metal Sample`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a nonzero coefficient, the order of 0 is 0.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `DimEnergy` (PhysLean)
- `BoundingSieve.one_le_y` (Mathlib)
- `Finpartition.energy` (Mathlib)
- `Filter.principal` (Mathlib)
- `NumberField.AdeleRing.principalSubgroup` (Mathlib)
- `Nat.nth_prime_zero_eq_two` (Mathlib)
- `StateTransition.Respects` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `StateTransition.Reaches₁` (Mathlib)
- `StateTransition.Reaches₁` (Mathlib)
- `Real.smoothTransition` (Mathlib)
- `StateTransition.FRespects` (Mathlib)
- `Mathlib.Meta.FunProp.withIncreasedTransitionDepth` (Mathlib)
- `Real.smoothTransition` (Mathlib)
- `StateTransition.FRespects` (Mathlib)
- `Polynomial.mem_lifts` (Mathlib)
- `RingHom.star_apply` (Mathlib)
- `ωCPO.omegaCompletePartialOrderEqualizer` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Finpartition.coe_energy` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0518.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.ElementIdentity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.FigureLineOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.FigureMarkerColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.HasPhysicalMetalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.IsUniqueMatchingMaximumWorkFunctionChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.MatchesMaximumConsistentWorkFunctionChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.MatchesPhotoelectronEjectionObservations`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.MatchesSearsiumScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.MetalSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SatisfiesTransitionAndPhotoelectricLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SearsiumEnergyLevel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SearsiumEnergyLevelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SearsiumPhotoelectricSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SearsiumPhoton`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0518.SearsiumTransition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
