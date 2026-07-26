# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0574.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0574.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:10e72abbb3c17f74c631ddfd234c8c9c29c0f755aa73117654082c751c8be058
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Chemical Element`
- `commutatorElement` | module `Mathlib.Algebra.Group.Commutator` | package Mathlib | The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `addCommutatorElement` | module `Mathlib.Algebra.Group.Commutator` | package Mathlib | The additive commutator of two elements `g₁` and `g₂`. This is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets

### Query: `atomic Number`
- `IsAtomic` | module `Mathlib.Order.Atoms` | package Mathlib | A lattice is atomic iff every element other than `⊥` has an atom below it.
- `OrderedFinpartition.atomic_length` | module `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` | package Mathlib | **Atomic Ordered Partition Length.** The length of the atomic ordered partition of a natural number $n$ is equal to $n$.
- `Mathlib.Tactic.Order.AtomicFact` | module `Mathlib.Tactic.Order.CollectFacts` | package Mathlib | A structure for storing facts about variables.

### Query: `Nuclear Isotope`
- `Nucleus.idempotent` | module `Mathlib.Order.Nucleus` | package Mathlib | **Idempotency of a Nucleus.** For any element $x$ in a meet-semilattice $X$, applying a nucleus $n$ twice to $x$ is equivalent to applying it once; that is, $n(n(x)) = n(x)$.
- `CategoryTheory.Iso` | module `Mathlib.CategoryTheory.Iso` | package Mathlib | An isomorphism (a.k.a. an invertible morphism) between two objects of a category. The inverse morphism is bundled. See also `CategoryTheory.Core` for the category with the same objects and isomorphisms playing the rol...
- `Nucleus.instFrameElemRangeCoe` | module `Mathlib.Order.Nucleus` | package Mathlib | **Frame Structure on the Range of a Nucleus.** The range of a nucleus $n$ on a frame forms a frame in its own right.

### Query: `proton Number`
- `SuperSymmetry.SU5.PotentialTerm.causeProtonDecay` | module `Physlib.Particles.SuperSymmetry.SU5.Potential` | package PhysLean | The finite set of terms in the superpotential and Kahler potential which are involved in proton decay. - `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` - `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` - `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd` - `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
- `Nat.fermatNumber` | module `Mathlib.NumberTheory.Fermat` | package Mathlib | Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`.
- `NumberField` | module `Mathlib.NumberTheory.NumberField.Basic` | package Mathlib | A number field is a field which has characteristic zero and is finite dimensional over ℚ.

### Query: `neptunium237`
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `radium225`
- `Ideal.radical` | module `Mathlib.RingTheory.Ideal.Operations` | package Mathlib | The radical of an ideal `I` consists of the elements `r` such that `r ^ n ∈ I` for some `n`.
- `UniqueFactorizationMonoid.radical` | module `Mathlib.RingTheory.Radical.Basic` | package Mathlib | The radical of an element `a` in a unique factorization monoid is the product of the prime factors of `a`.
- `Nat.fermatNumber_two` | module `Mathlib.NumberTheory.Fermat` | package Mathlib | **The Second Fermat Number.** The second Fermat number, defined as $2^{2^2} + 1$, is equal to $17$.

### Query: `actinium229`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.

### Query: `actinium225`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `SMRHN.SM.perm` | module `Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.Basic` | package PhysLean | The permutations acting on the ACC system corresponding to the SM with RHN.

### Query: `thorium223`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `commutatorElement` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `addCommutatorElement` (Mathlib)
- `IsAtomic` (Mathlib)
- `OrderedFinpartition.atomic_length` (Mathlib)
- `Mathlib.Tactic.Order.AtomicFact` (Mathlib)
- `Nucleus.idempotent` (Mathlib)
- `CategoryTheory.Iso` (Mathlib)
- `Nucleus.instFrameElemRangeCoe` (Mathlib)
- `SuperSymmetry.SU5.PotentialTerm.causeProtonDecay` (PhysLean)
- `Nat.fermatNumber` (Mathlib)
- `NumberField` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Ideal.radical` (Mathlib)
- `UniqueFactorizationMonoid.radical` (Mathlib)
- `Nat.fermatNumber_two` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `SMRHN.SM.perm` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0574.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.ChemicalElement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.DecayMode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.DecayPathPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.DecaySchemeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.DecayStep`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.FiveStepDecayScheme`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.IsDecayProduct`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.MatchesSuppliedDecayFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.NuclearIsotope`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.NuclearPlotQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.PlotAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0574.SatisfiesDecayNumberLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
