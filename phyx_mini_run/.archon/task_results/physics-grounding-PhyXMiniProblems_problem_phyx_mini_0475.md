# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0475.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0475.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8f78cf5c9a6cfa6a17410dc249bfdf0a3508261cbb6076c6e93839550283f712
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `volume Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `BoxIntegral.Box.volume_face_mul` | module `Mathlib.Analysis.BoxIntegral.Partition.Measure` | package Mathlib | **Volume of a Box as a Product of Face Volume and Side Length.** For a rectangular box $I$ in $\mathbb{R}^{n+1}$ and any index $i \in \{0, \dots, n\}$, the volume of $I$ (defined as the product of its side lengths $\p...

### Query: `energy Dimension`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `entropy Dimension`
- `Real.binEntropy` | module `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` | package Mathlib | The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function) `binEntropy p := - p * log p - (1-p) * log (1 - p)` is the Shannon entropy of a Bernoulli random variable with success probability `p`.
- `entropy` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Entropy of a monophase ideal gas: S(U,V,N) = N s0 + N R (c log(U/U0) + log(V/V0) - (c+1) log(N/N0)).
- `MicroHamiltonian.entropyS` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.ThermoQuantities` | package PhysLean | The entropy, defined as the -∂A/∂T. Function of T.

### Query: `Volume`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `HahnSeries.leadingCoeff` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or zero if the series vanishes.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `Energy`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `Thermodynamic Entropy`
- `Real.binEntropy` | module `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` | package Mathlib | The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function) `binEntropy p := - p * log p - (1-p) * log (1 - p)` is the Shannon entropy of a Bernoulli random variable with success probability `p`.
- `CanonicalEnsemble.thermodynamicEntropy` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The absolute thermodynamic entropy, defined from its statistical mechanical foundation as the Gibbs-Shannon entropy of the dimensionless physical probability distribution. This corresponds to Landau & Lifshitz, Statis...
- `CanonicalEnsemble.thermodynamicEntropy_def` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | **Definition of Thermodynamic Entropy.** For a canonical ensemble $\mathcal{C}$ at temperature $T$, the thermodynamic entropy is defined as the product of the negative Boltzmann constant $-k_B$ and the integral of the...

### Query: `Molar Gas Constant`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.

### Query: `Ideal Gas State`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `IdealGas.ZIntegrable` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | **Integrability of the Ideal Gas Partition Function.** For a system of $n$ particles in a volume $V > 0$ at an inverse temperature $\beta > 0$, the ideal gas Hamiltonian is $Z$-integrable. This means that the Boltzman...

### Query: `Ideal Gas Entropy Parameters`
- `Real.binEntropy` | module `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` | package Mathlib | The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function) `binEntropy p := - p * log p - (1-p) * log (1 - p)` is the Shannon entropy of a Bernoulli random variable with success probability `p`.
- `entropy` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Entropy of a monophase ideal gas: S(U,V,N) = N s0 + N R (c log(U/U0) + log(V/V0) - (c+1) log(N/N0)).
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `BoxIntegral.Box.volume_face_mul` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy` (PhysLean)
- `Real.binEntropy` (Mathlib)
- `entropy` (PhysLean)
- `MicroHamiltonian.entropyS` (PhysLean)
- `Real.volume_real_Ico` (Mathlib)
- `HahnSeries.leadingCoeff` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `DimEnergy` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finpartition.energy` (Mathlib)
- `Real.binEntropy` (Mathlib)
- `CanonicalEnsemble.thermodynamicEntropy` (PhysLean)
- `CanonicalEnsemble.thermodynamicEntropy_def` (PhysLean)
- `LocallyConstant` (Mathlib)
- `IdealGas` (PhysLean)
- `Constants.kB` (PhysLean)
- `IdealGas.ideal_gas_law` (PhysLean)
- `IdealGas` (PhysLean)
- `IdealGas.ZIntegrable` (PhysLean)
- `Real.binEntropy` (Mathlib)
- `entropy` (PhysLean)
- `IdealGas` (PhysLean)

## Local abstractions introduced

- `PhyXMini0475.Energy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.FreeExpansionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.IdealGasEntropyParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.IdealGasState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.MolarGasConstant`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.ThermodynamicEntropy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMini0475.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
