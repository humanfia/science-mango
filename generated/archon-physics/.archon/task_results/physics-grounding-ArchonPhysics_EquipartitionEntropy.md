# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/EquipartitionEntropy.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_EquipartitionEntropy.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:5555b9ef17d302f782d1f2fd485a11bca9a5285ce0fb76af4cd9ccb36e8c318b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `late Window Average`
- `MeasureTheory.average` | module `Mathlib.MeasureTheory.Integral.Average` | package Mathlib | Average value of a function `f` w.r.t. a measure `μ`, denoted `⨍ x, f x ∂μ`. It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is...
- `Real.circleAverage` | module `Mathlib.MeasureTheory.Integral.CircleAverage` | package Mathlib | Define `circleAverage f c R` as the average value of `f` on the circle with center `c` and radius `R`. This is a real notion, which should not be confused with the complex path integral notion defined in `circleIntegr...
- `Mathlib.Linter.Style.Whitespace.mkWindow` | module `Mathlib.Tactic.Linter.Whitespace` | package Mathlib | `mkWindow orig start ctx` extracts from `orig` a string that starts at the first non-whitespace character before `start`, then expands to cover `ctx` more characters and continues still until the first non-whitespace...

### Query: `late Window Average nonneg`
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Nonnegative squared frequency gives nonnegative modal energy.
- `ArchonPhysics.HarmonicModes.modeFrequencySq_nonneg` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Spectral squared frequencies of a positive-semidefinite harmonic matrix are nonnegative.
- `ArchonPhysics.Lattice.kineticEnergy_nonneg` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Kinetic energy is nonnegative for a pointwise strictly positive mass profile.

### Query: `total Weight`
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.

### Query: `normalized Weights`
- `Affine.Simplex.excenterWeights` | module `Mathlib.Geometry.Euclidean.Incenter` | package Mathlib | The normalized weights of the vertices in an affine combination that gives an excenter with signs determined by the given set of indices. An excenter with those signs exists if and only if the sum of these weights is 1.
- `UniqueFactorizationMonoid.normalizedFactors` | module `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors` | package Mathlib | Noncomputably determines the multiset of prime factors.
- `Finset.centroidWeights` | module `Mathlib.LinearAlgebra.AffineSpace.Centroid` | package Mathlib | The weights for the centroid of some points.

### Query: `window Weights spec`
- `ArchonPhysics.HamiltonianScaling.rescalingData_spec` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Formula-level specification of the Hamiltonian, rescaling, and coupling.
- `ArchonPhysics.HarmonicModes.harmonicData_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Formula-level specification of the mass-weighted operator and one mode.
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The oscillator adapter has unit mass and spring constant `omega²`.

### Query: `sum normalized Weights`
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.
- `ArchonPhysics.HarmonicModes.differenceMatrix_mulVec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The matrix realization of the periodic forward difference.

### Query: `uniform Weights`
- `Finset.centroidWeights` | module `Mathlib.LinearAlgebra.AffineSpace.Centroid` | package Mathlib | The weights for the centroid of some points.
- `UniformContinuous` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then `f x` is close to `f y` no matter whe...
- `IsUniformGroup.isLeftUniformGroup` | module `Mathlib.Topology.Algebra.IsUniformGroup.Defs` | package Mathlib | **Uniform Group is a Left-Uniform Group.** Every uniform group is a left-uniform group, meaning that its uniform structure is equivalent to the left uniformity, where the uniformity filter is the pullback of the neigh...

### Query: `l1Distance`
- `MeasureTheory.L1.dist_def` | module `Mathlib.MeasureTheory.Function.L1Space.AEEqFun` | package Mathlib | **Distance in $L^1$.** For any two functions $f$ and $g$ in the space $L^1(\mu)$, the distance between them is defined as the real-valued integral of the pointwise extended distance between $f(a)$ and $g(a)$ with resp...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `l1Distance normalized uniform le two`
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.
- `ArchonPhysics.HarmonicModes.modalEnergy` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Energy of a real harmonic mode with squared frequency `omegaSq`.

### Query: `Approx Equipartition`
- `Finpartition.IsEquipartition` | module `Mathlib.Order.Partition.Equipartition` | package Mathlib | An equipartition is a partition whose parts are all the same size, up to a difference of `1`.
- `MeasureTheory.SimpleFunc.approxOn` | module `Mathlib.MeasureTheory.Function.SimpleFuncDense` | package Mathlib | Approximate a measurable function by a sequence of simple functions `F n` such that `F n x ∈ s`.
- `Finpartition.equitabilise_isEquipartition` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise` | package Mathlib | **Equitability of the Equitabilised Partition.** The partition obtained by equitabilising a finite partition is an equipartition; that is, the sizes of all its constituent parts differ by at most one.

## Grounded Mathlib/PhysLean names

- `MeasureTheory.average` (Mathlib)
- `Real.circleAverage` (Mathlib)
- `Mathlib.Linter.Style.Whitespace.mkWindow` (Mathlib)
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modeFrequencySq_nonneg` (ArchonPhysics)
- `ArchonPhysics.Lattice.kineticEnergy_nonneg` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)
- `Affine.Simplex.excenterWeights` (Mathlib)
- `UniqueFactorizationMonoid.normalizedFactors` (Mathlib)
- `Finset.centroidWeights` (Mathlib)
- `ArchonPhysics.HamiltonianScaling.rescalingData_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.harmonicData_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.differenceMatrix_mulVec` (ArchonPhysics)
- `Finset.centroidWeights` (Mathlib)
- `UniformContinuous` (Mathlib)
- `IsUniformGroup.isLeftUniformGroup` (Mathlib)
- `MeasureTheory.L1.dist_def` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy` (ArchonPhysics)
- `Finpartition.IsEquipartition` (Mathlib)
- `MeasureTheory.SimpleFunc.approxOn` (Mathlib)
- `Finpartition.equitabilise_isEquipartition` (Mathlib)

## Local abstractions introduced

- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
