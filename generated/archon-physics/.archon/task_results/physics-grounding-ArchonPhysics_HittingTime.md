# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/HittingTime.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_HittingTime.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:01df6df957554d252a11e4ad3ef2aa864e1876921902fafed8da391ff3fdbdc0
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `hitting Times`
- `MeasureTheory.hittingBtwn_mem_Icc` | module `Mathlib.Probability.Process.HittingTime` | package Mathlib | **Hitting Time Range.** For any two time points $n$ and $m$ such that $n \le m$, the hitting time of a set $s$ by a process $u$ between $n$ and $m$ is contained within the closed interval $[n, m]$.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MeasureTheory.hittingBtwn` | module `Mathlib.Probability.Process.HittingTime` | package Mathlib | Hitting time: given a stochastic process `u` and a set `s`, `hittingBtwn u s n m` is the first time `u` is in `s` after time `n` and before time `m` (if `u` does not hit `s` after time `n` and before `m` then the hitt...

### Query: `first Hitting Time`
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-time average of the modal energy in the interval `[mu * T, T]`.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.

### Query: `hitting spec`
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of approximate equipartition and its observables.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Spectral entropy, with Mathlib's `negMulLog` convention at zero.

### Query: `first Hitting Time empty`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of approximate equipartition and its observables.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.

### Query: `first Hitting Time le of mem`
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Entropy of a finite probability vector is between zero and `log(card)`.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform finite weights attain the maximal spectral entropy.

### Query: `first Hitting Time mono`
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-time average of the modal energy in the interval `[mu * T, T]`.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.

### Query: `not event before first Hitting Time`
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-time average of the modal energy in the interval `[mu * T, T]`.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.

### Query: `Persists For`
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform finite weights attain the maximal spectral entropy.
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform weights on a finite mode set.

### Query: `persistence Times`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order_le_of_coeff_ne_zero` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Order Bound for Hahn Series.** For any Hahn series $x$ over a linearly ordered set $\Gamma$, if the coefficient of $x$ at an index $g \in \Gamma$ is non-zero, then the order of $x$ is less than or equal to $g$.

### Query: `persistence Time`
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-time average of the modal energy in the interval `[mu * T, T]`.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.

## Grounded Mathlib/PhysLean names

- `MeasureTheory.hittingBtwn_mem_Icc` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MeasureTheory.hittingBtwn` (Mathlib)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` (ArchonPhysics)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order_le_of_coeff_ne_zero` (Mathlib)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.HittingTime.PersistsFor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
