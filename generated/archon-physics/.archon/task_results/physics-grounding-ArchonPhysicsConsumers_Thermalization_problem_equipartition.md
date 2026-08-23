# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_equipartition.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_equipartition.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c9782ed05e080fdbb509d0f8794a0daf3df67c43c164c3279c7722e10da2ba85
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Nonnegative modal energies`
- `ArchonPhysics.HarmonicModes.modalEnergy_conserved` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | A differentiable real harmonic mode conserves its modal energy.
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Nonnegative squared frequency gives nonnegative modal energy.
- `ArchonPhysics.HarmonicModes.modalEnergy` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Energy of a real harmonic mode with squared frequency `omegaSq`.

### Query: `Late window average`
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-time average of the modal energy in the interval `[mu * T, T]`.
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage_nonneg` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The late-window average of a pointwise nonnegative energy is nonnegative.
- `ArchonPhysics.EquipartitionEntropy.windowWeights_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the window average and normalized weights.

### Query: `Total monitored energy`
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The existing finite lattice Hamiltonian evaluated on phase space ordered as `(q, p)`.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Energy agrees at the endpoints of any segment carrying the microscopic ODE.
- `ArchonPhysics.EquipartitionEntropy.totalWeight` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The total of a finite collection of modal weights.

### Query: `Normalized modal weight`
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Weights normalized by their total.
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Positive total weight makes the normalized finite weights sum to one.
- `ArchonPhysics.EquipartitionEntropy.totalWeight` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The total of a finite collection of modal weights.

### Query: `Distance from equal sharing`
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.l1Distance` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The finite `ℓ¹` distance between two weight functions.
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Positive total weight makes the normalized finite weights sum to one.

### Query: `Approximate equipartition`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of approximate equipartition and its observables.

### Query: `Finite normalized weights have distance at most two`
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Positive total weight makes the normalized finite weights sum to one.
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Weights normalized by their total.

### Query: `Modal Energies`
- `ArchonPhysics.HarmonicModes.modalEnergy` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Energy of a real harmonic mode with squared frequency `omegaSq`.
- `ArchonPhysics.HarmonicModes.modalEnergy_conserved` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | A differentiable real harmonic mode conserves its modal energy.
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Nonnegative squared frequency gives nonnegative modal energy.

### Query: `total Energy`
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The existing finite lattice Hamiltonian evaluated on phase space ordered as `(q, p)`.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Energy agrees at the endpoints of any segment carrying the microscopic ODE.
- `ArchonPhysics.EquipartitionEntropy.totalWeight` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The total of a finite collection of modal weights.

### Query: `normalized Weight`
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Weights normalized by their total.
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Positive total weight makes the normalized finite weights sum to one.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.HarmonicModes.modalEnergy_conserved` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.lateWindowAverage_nonneg` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.windowWeights_spec` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.totalWeight` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.totalWeight` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.equipartition_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy_conserved` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modalEnergy_nonneg` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.totalWeight` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.Equipartition.ApproximatelyEquipartitioned`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.Equipartition.ModalEnergies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
