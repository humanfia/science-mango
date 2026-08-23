# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_microscopic_dynamics.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_microscopic_dynamics.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:dca375abff95ddb8c9c031b7b6deb98f24607148827a5179ea91dd4f7dec6e54
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `Unique local solution-germ property`
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | For every initial state and time, the concrete microscopic ODE has a solution on a nontrivial symmetric interval and the resulting solution germ is unique.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.

### Query: `Finite microscopic-dynamics formalization target`
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | A classical solution of the microscopic vector field defined for every real time.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite lattice Hamiltonian has derivative zero whenever the vector ODE holds.
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite microscopic vector field is continuously differentiable.

### Query: `Has Unique Local Solution Germ`
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | For every initial state and time, the concrete microscopic ODE has a solution on a nontrivial symmetric interval and the resulting solution germ is unique.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.

### Query: `microscopic dynamics physics formalization target`
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | A classical solution of the microscopic vector field defined for every real time.
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | For every initial state and time, the concrete microscopic ODE has a solution on a nontrivial symmetric interval and the resulting solution germ is unique.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.MicroscopicDynamics.HasUniqueLocalSolutionGerm`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
