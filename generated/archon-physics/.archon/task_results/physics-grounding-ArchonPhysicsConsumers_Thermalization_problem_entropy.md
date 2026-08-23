# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_entropy.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_entropy.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:304de2125ee03e3ab3c6f9fdd9244ac2d70cf570879783229558c81ac4088412
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Zero-safe entropy summand`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Spectral entropy, with Mathlib's `negMulLog` convention at zero.

### Query: `Spectral entropy`
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Spectral entropy, with Mathlib's `negMulLog` convention at zero.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Entropy of a finite probability vector is between zero and `log(card)`.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform finite weights attain the maximal spectral entropy.

### Query: `Entropy deficit`
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy deficit from the uniform finite distribution.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Spectral entropy, with Mathlib's `negMulLog` convention at zero.

### Query: `Participation number`
- `ArchonPhysics.EquipartitionEntropy.participationNumber` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy-derived effective number of occupied modes.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy deficit from the uniform finite distribution.

### Query: `Uniform weights`
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform weights on a finite mode set.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Weights normalized by their total.

### Query: `Entropy is nonnegative and uniform weights attain its finite value`
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform weights on a finite mode set.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform finite weights attain the maximal spectral entropy.

### Query: `entropy Summand`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy deficit from the uniform finite distribution.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.

### Query: `uniform Weight`
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Uniform weights on a finite mode set.
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The normalized weight vector is at `ℓ¹` distance at most two from uniform.
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Weights normalized by their total.

### Query: `entropy physics formalization target`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy deficit from the uniform finite distribution.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.participationNumber` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_uniform` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.uniformWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.l1Distance_normalized_uniform_le_two` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
