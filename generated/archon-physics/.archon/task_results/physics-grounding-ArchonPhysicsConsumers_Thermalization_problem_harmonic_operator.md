# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_harmonic_operator.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_harmonic_operator.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b7842fc1067e9211d6ef84bb6f144a1c31fd53291b1fe4043c48ddf680105877
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The unit-mass Physlib oscillator associated with a positive mode frequency.
- `ArchonPhysics.HarmonicModes.modeFrequencySq` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The spectral squared frequency of the selected normal mode.
- `ArchonPhysics.HarmonicModes.modeFrequencySq_nonneg` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Spectral squared frequencies of a positive-semidefinite harmonic matrix are nonnegative.

### Query: `Real.sqrt square root`
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.Lattice.sqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the square root of the mass profile.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `Finite field`
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite microscopic vector field is continuously differentiable.
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The autonomous microscopic vector field on `(q, p)` phase space.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Entropy of a finite probability vector is between zero and `log(card)`.

### Query: `Inverse square-root mass`
- `ArchonPhysics.Lattice.inverseMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse mass profile.
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.

### Query: `Dynamical matrix`
- `ArchonPhysics.HarmonicModes.differenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The matrix of the periodic forward nearest-neighbour difference.
- `ArchonPhysics.HarmonicModes.differenceMatrix_mulVec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The matrix realization of the periodic forward difference.
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.

### Query: `Self-adjoint predicate`
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Positive total weight makes the normalized finite weights sum to one.
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.

### Query: `Positive-semidefinite predicate`
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The unit-mass Physlib oscillator associated with a positive mode frequency.
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The oscillator adapter has unit mass and spring constant `omega²`.
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | A positive normal-mode oscillator conserves Physlib's energy along its equation of motion.

### Query: `Minimal zero-mode interface`
- `ArchonPhysics.HarmonicModes.translationMode_is_zero` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The translation vector lies in the kernel of the harmonic matrix.
- `ArchonPhysics.HarmonicModes.translationMode_ne_zero` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Positive masses make the translation vector nonzero.
- `ArchonPhysics.HarmonicModes.harmonicData_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Formula-level specification of the mass-weighted operator and one mode.

### Query: `Harmonic flow`
- `ArchonPhysics.HarmonicModes.harmonicData_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | Formula-level specification of the mass-weighted operator and one mode.
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.HarmonicModes.positiveModeOscillator` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modeFrequencySq` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.modeFrequencySq_nonneg` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.sqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.differenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.differenceMatrix_mulVec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.sum_normalizedWeights` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.translationMode_is_zero` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.translationMode_ne_zero` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.harmonicData_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.harmonicData_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.HarmonicOperator.Field`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.HarmonicOperator.HarmonicFlow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.HarmonicOperator.IsPositiveSemidefinite`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.HarmonicOperator.IsSelfAdjoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.HarmonicOperator.NormalModeDiagonalization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
