# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_kinetic_time_rescaling.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_kinetic_time_rescaling.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:fd988eb90088d771fa8ffeaee81ac9347838432b47dddb7ca952f71a10d3b336
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `Effective kinetic model`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `Kinetic solution`
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `State-event first hit`
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | No strictly positive event can occur strictly before the first hitting time.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The first strictly positive real time at which a state predicate holds.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The state-event hitting time is the infimum of its strictly positive event times.

### Query: `Current microscopic formula placeholder`
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | The concrete vector-valued Hamilton ODE holds at the specified time.
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | A classical solution of the microscopic vector field defined for every real time.
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` | module `ArchonPhysics.MicroscopicDynamics` | package ArchonPhysics | For every initial state and time, the concrete microscopic ODE has a solution on a nontrivial symmetric interval and the resulting solution germ is unique.

### Query: `Conditional effective solution and hitting-time rescaling`
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The first strictly positive real time at which a state predicate holds.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The state-event hitting time is the infimum of its strictly positive event times.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Transporting a trajectory by `g^2` rescales its state-event hitting time by `g⁻²`.

### Query: `Solves Kinetic Equation`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.

### Query: `first Hitting Time`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

### Query: `microscopic Equilibration Time Scaling Conjecture`
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The first strictly positive real time at which a state predicate holds.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The state-event hitting time is the infimum of its strictly positive event times.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Transporting a trajectory by `g^2` rescales its state-event hitting time by `g⁻²`.

### Query: `kinetic time rescaling physics formalization target`
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The first strictly positive real time at which a state predicate holds.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The state-event hitting time is the infimum of its strictly positive event times.
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Transporting a trajectory by `g^2` rescales its state-event hitting time by `g⁻²`.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.HittingTime.not_event_before_firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsClassicalSolutionAt` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.IsGlobalClassicalSolution` (ArchonPhysics)
- `ArchonPhysics.MicroscopicDynamics.exists_unique_local_solution_germ` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_eq_sInf` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.firstStateHittingTime_rescale` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.KineticTimeRescaling.EffectiveKineticModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `ArchonPhysics.Generated.KineticTimeRescaling.SolvesKineticEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
