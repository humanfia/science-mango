# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0372.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0372.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b96190398faec7839bbee1b9cc4100f95710c253250f9d897dd650a2421b2483
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Gas Species`
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `SMRHN.toSpecies_familyUniversal` | module `Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps` | package PhysLean | **Species Consistency of the Universal Family.** For any natural number $n$, any index $j \in \{0, \dots, 5\}$, any charge $S$ of type $\text{SM}\nu$, and any index $i \in \{0, \dots, n-1\}$, the $j$-th species of the...

### Query: `Gas Sample`
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Plausible.PNat.sampleableExt` | module `Mathlib.Testing.Plausible.Sampleable` | package Mathlib | **Sampleability of Positive Natural Numbers.** The type of positive natural numbers $\mathbb{N}^+$ is equipped with an instance for external sampling, allowing for the generation and shrinking of values during testing.

### Query: `PVState`
- `ωCPO.omegaCompletePartialOrderEqualizer` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **$\omega$-Complete Partial Order on Equalizers.** Given two $\omega$-complete partial orders $\alpha$ and $\beta$ and two continuous functions $f, g: \alpha \to \beta$, the equalizer $\{ a \in \alpha \mid f(a) = g(a)...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `ωCPO.instLargeCategory` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **The Category of $\omega$-Complete Partial Orders.** The collection of $\omega$-complete partial orders forms a large category where the morphisms between two objects are the continuous functions between them, the id...

### Query: `Three State Process`
- `MeasureTheory.stoppedProcess` | module `Mathlib.Probability.Process.Stopping` | package Mathlib | Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if `i ≤ τ ω`, and `u (τ ω) ω` otherwise. Intuitively, the stopped process stops evolving once the stopping time has occurred.
- `ThreeGPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3GP-free** if it does not contain any non-trivial geometric progression of length three.
- `ThreeAPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3AP-free** if it does not contain any non-trivial arithmetic progression of length three. This is also sometimes called a **non-averaging set** or **Salem-Spencer set**.

### Query: `Ideal Gas Parameters`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `Ideal` | module `Mathlib.RingTheory.Ideal.Defs` | package Mathlib | A (left) ideal in a semiring `R` is an additive submonoid `s` such that `a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.
- `Ideal.span` | module `Mathlib.RingTheory.Ideal.Span` | package Mathlib | The ideal generated by a subset of a ring

### Query: `Satisfies Mass Mole Relation`
- `UnitExamples.EnergyMass` | module `Physlib.Units.Examples` | package PhysLean | The equation `E = m c^2`, in this equation we `E` and `m` are implicitly in the units `u`, while the speed of light is explicitly written in those units.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `Module.Presentation.tautological.R.add` | module `Mathlib.Algebra.Module.Presentation.Tautological` | package Mathlib | **Tautological Sum Relation.** For any two elements $m_1$ and $m_2$ in a module $M$, there exists a formal relation representing their sum.

### Query: `Satisfies Ideal Gas Equation`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `Ideal.span` | module `Mathlib.RingTheory.Ideal.Span` | package Mathlib | The ideal generated by a subset of a ring
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.

### Query: `temperature In Degrees Celsius`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `state One Temperature from helium Data`
- `Temperature.instZero` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | **Zero Temperature.** The type of temperatures has a zero element, defined as the temperature with a value of $0$.
- `Temperature.betaFromReal` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | Map a real `t` to the inverse temperature `β` corresponding to the temperature `Real.toNNReal t` (`max t 0`), returned as a real number.
- `Dimension.one_temperature` | module `Physlib.Units.Dimension` | package PhysLean | **Temperature Dimension of Unity.** The temperature dimension of the identity dimension $1$ is equal to $0$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `TensorSpecies.Tensor` (PhysLean)
- `IdealGas` (PhysLean)
- `SMRHN.toSpecies_familyUniversal` (PhysLean)
- `IdealGas` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Plausible.PNat.sampleableExt` (Mathlib)
- `ωCPO.omegaCompletePartialOrderEqualizer` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `ωCPO.instLargeCategory` (Mathlib)
- `MeasureTheory.stoppedProcess` (Mathlib)
- `ThreeGPFree` (Mathlib)
- `ThreeAPFree` (Mathlib)
- `IdealGas.ideal_gas_law` (PhysLean)
- `Ideal` (Mathlib)
- `Ideal.span` (Mathlib)
- `UnitExamples.EnergyMass` (PhysLean)
- `MassUnit` (PhysLean)
- `Module.Presentation.tautological.R.add` (Mathlib)
- `IdealGas.ideal_gas_law` (PhysLean)
- `Ideal.span` (Mathlib)
- `IdealGas` (PhysLean)
- `MvPolynomial.degrees` (Mathlib)
- `Temperature` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `Temperature.instZero` (PhysLean)
- `Temperature.betaFromReal` (PhysLean)
- `Dimension.one_temperature` (PhysLean)

## Local abstractions introduced

- `PhyXMini0372.GasSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.GasSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.IdealGasParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.PVState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.SatisfiesIdealGasEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.SatisfiesMassMoleRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0372.ThreeStateProcess`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
