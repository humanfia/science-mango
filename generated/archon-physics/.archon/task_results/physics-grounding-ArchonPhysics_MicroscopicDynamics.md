# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/MicroscopicDynamics.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_MicroscopicDynamics.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f6abe168afde634614fd601c18f8f5af9339c97455d6000496aa357593d54ada
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `Phase Space`
- `ArchonPhysics.MicroscopicDynamics.PhaseSpace` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Position--momentum phase space of the finite periodic chain, ordered as `(q, p)`.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.

### Query: `interaction Potential`
- `ArchonPhysics.MicroscopicDynamics.interactionPotential` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The degree-`n` single-bond potential `x²/2 + λ xⁿ/n`.
- `ArchonPhysics.MicroscopicDynamics.interactionForce` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The derivative formula `x + λ xⁿ⁻¹` for a nonzero degree `n`.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite lattice Hamiltonian has derivative zero whenever the vector ODE holds.

### Query: `interaction Force`
- `ArchonPhysics.MicroscopicDynamics.interactionForce` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The derivative formula `x + λ xⁿ⁻¹` for a nonzero degree `n`.
- `ArchonPhysics.MicroscopicDynamics.latticeForce` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The periodic nearest-neighbour force acting on every lattice site.
- `ArchonPhysics.MicroscopicDynamics.latticeForce_apply` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Pointwise expansion of the outgoing-minus-incoming nearest-neighbour force.

### Query: `lattice Force`
- `ArchonPhysics.MicroscopicDynamics.latticeForce` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The periodic nearest-neighbour force acting on every lattice site.
- `ArchonPhysics.MicroscopicDynamics.latticeForce_apply` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Pointwise expansion of the outgoing-minus-incoming nearest-neighbour force.
- `ArchonPhysics.MicroscopicDynamics.sum_latticeForce` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Internal nearest-neighbour forces sum to zero on the periodic chain.

### Query: `microscopic Vector Field`
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The autonomous microscopic vector field on `(q, p)` phase space.
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite microscopic vector field is continuously differentiable.
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.

### Query: `Is Classical Solution At`
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | A classical solution of the microscopic vector field defined for every real time.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.

### Query: `Is Global Classical Solution`
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | A classical solution of the microscopic vector field defined for every real time.
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | For every initial state and time, the concrete microscopic ODE has a solution on a nontrivial symmetric interval and the resulting solution germ is unique.

### Query: `hamiltonian Energy`
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The existing finite lattice Hamiltonian evaluated on phase space ordered as `(q, p)`.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Energy agrees at the endpoints of any segment carrying the microscopic ODE.
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The finite lattice Hamiltonian has derivative zero whenever the vector ODE holds.

### Query: `total Momentum`
- `ArchonPhysics.MicroscopicDynamics.totalMomentum` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Total canonical momentum of a finite periodic-chain state.
- `ArchonPhysics.MicroscopicDynamics.totalMomentum_eq_of_forall_mem_uIcc` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Total momentum agrees at the endpoints of any segment carrying the microscopic ODE.
- `ArchonPhysics.MicroscopicDynamics.totalMomentum_hasDerivAt_zero_at` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | Total momentum has derivative zero whenever the concrete microscopic ODE holds.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.PhaseSpace` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.interactionPotential` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.interactionForce` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.interactionForce` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.latticeForce` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.latticeForce_apply` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.latticeForce` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.latticeForce_apply` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.sum_latticeForce` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.microscopicVectorField_contDiff` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_eq_of_forall_mem_uIcc` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.hamiltonianEnergy_hasDerivAt_zero_at` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.totalMomentum` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.totalMomentum_eq_of_forall_mem_uIcc` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.totalMomentum_hasDerivAt_zero_at` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.MicroscopicDynamics.PhaseSpace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
