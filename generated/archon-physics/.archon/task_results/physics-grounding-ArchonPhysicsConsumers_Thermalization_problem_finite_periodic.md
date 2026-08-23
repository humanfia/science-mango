# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_finite_periodic.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_finite_periodic.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c185e20a4755600c9d003a418bf208fc8e8807e3ed07b8dd7d18e4b3aa271914
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Periodic site`
- `ArchonPhysics.Lattice.Site` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The sites of a finite periodic chain of length `N`.
- `ArchonPhysics.Lattice.siteConfiguration_spec` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The locked concrete realization of sites and configurations.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The finite periodic-chain Hamiltonian with degree-`n` nearest-neighbour interaction.

### Query: `Real lattice field`
- `ArchonPhysics.Lattice.Configuration` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Real-valued configurations on the periodic sites.
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.

### Query: `Finite positive-mass lattice`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The mass at each periodic site.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Every site has strictly positive mass.

### Query: `Forward difference`
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.
- `ArchonPhysics.Lattice.forwardDifference_apply` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise expansion of the periodic forward difference.
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.

### Query: `Total forward difference`
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.
- `ArchonPhysics.Lattice.forwardDifference_apply` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise expansion of the periodic forward difference.
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.

### Query: `Kinetic quadratic form`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `Positive masses and cyclic telescoping`
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The unit-mass Physlib oscillator associated with a positive mode frequency.
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The oscillator adapter has unit mass and spring constant `omega²`.
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | A positive normal-mode oscillator conserves Physlib's energy along its equation of motion.

### Query: `Site`
- `ArchonPhysics.Lattice.Site` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The sites of a finite periodic chain of length `N`.
- `ArchonPhysics.Lattice.siteConfiguration_spec` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The locked concrete realization of sites and configurations.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The finite periodic-chain Hamiltonian with degree-`n` nearest-neighbour interaction.

### Query: `Field`
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The autonomous microscopic vector field on `(q, p)` phase space.
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite microscopic vector field is continuously differentiable.
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` | module `ArchonPhysics.EquipartitionEntropy` | package ArchonPhysics | Entropy of a finite probability vector is between zero and `log(card)`.

### Query: `Lattice`
- `ArchonPhysics.Lattice.Configuration` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Real-valued configurations on the periodic sites.
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The mass at each periodic site.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.Site` (ArchonPhysics)
- `ArchonPhysics.Lattice.siteConfiguration_spec` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` (ArchonPhysics)
- `ArchonPhysics.Lattice.Configuration` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference_apply` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference_apply` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` (ArchonPhysics)
- `ArchonPhysics.Lattice.Site` (ArchonPhysics)
- `ArchonPhysics.Lattice.siteConfiguration_spec` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` (ArchonPhysics)
- `ArchonPhysics.EquipartitionEntropy.spectralEntropy_bounds` (ArchonPhysics)
- `ArchonPhysics.Lattice.Configuration` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.FinitePeriodic.Field`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.FinitePeriodic.Lattice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.FinitePeriodic.Site`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
