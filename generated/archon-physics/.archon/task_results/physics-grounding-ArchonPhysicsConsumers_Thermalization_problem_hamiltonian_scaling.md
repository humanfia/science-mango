# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_hamiltonian_scaling.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_hamiltonian_scaling.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c952d1da2baeda55c7d496b6ebd1f24247c52a936120dbf2836f60c11973c466
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.Lattice.sqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the square root of the mass profile.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.

### Query: `Sites and fields`
- `ArchonPhysics.Lattice.Configuration` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Real-valued configurations on the periodic sites.
- `ArchonPhysics.Lattice.siteConfiguration_spec` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The locked concrete realization of sites and configurations.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.

### Query: `Real fields`
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Approximate equipartition on a positive late window.
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | The entropy deficit from the uniform finite distribution.
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Formula-level specification of the entropy diagnostics.

### Query: `Forward difference`
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.
- `ArchonPhysics.Lattice.forwardDifference_apply` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise expansion of the periodic forward difference.
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.

### Query: `Finite polynomial Hamiltonian`
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The coupling after extracting a positive energy scale.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The finite periodic-chain Hamiltonian with degree-`n` nearest-neighbour interaction.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.

### Query: `Field rescaling`
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.

### Query: `Effective coupling`
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The coupling after extracting a positive energy scale.
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling_inv_sq` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The inverse-square effective-coupling law; this is algebraic only.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.

### Query: `Exact finite algebraic rescaling`
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Transporting a trajectory by `g^2` rescales its state-event hitting time by `g⁻²`.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `Site`
- `ArchonPhysics.Lattice.Site` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The sites of a finite periodic chain of length `N`.
- `ArchonPhysics.Lattice.siteConfiguration_spec` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The locked concrete realization of sites and configurations.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The finite periodic-chain Hamiltonian with degree-`n` nearest-neighbour interaction.

### Query: `Field`
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The autonomous microscopic vector field on `(q, p)` phase space.
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite microscopic vector field is continuously differentiable.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Entropy of a finite probability vector is between zero and `log(card)`.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.sqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.Lattice.Configuration` (ArchonPhysics)
- `ArchonPhysics.Lattice.siteConfiguration_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.ApproxEquipartition` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDeficit` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.entropyDiagnostics_spec` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference_apply` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling_inv_sq` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.Lattice.Site` (ArchonPhysics)
- `ArchonPhysics.Lattice.siteConfiguration_spec` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.HamiltonianScaling.Field`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.HamiltonianScaling.Site`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
