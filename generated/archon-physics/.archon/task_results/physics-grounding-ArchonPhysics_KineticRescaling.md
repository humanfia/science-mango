# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/KineticRescaling.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_KineticRescaling.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:aef6afda924a041891158c1eaa440c5993ece49545b2b96ac163222cfb7ac767
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `Solves Kinetic Equation`
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.
- `ArchonPhysics.Lattice.kineticEnergy` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The finite kinetic energy `∑ᵢ pᵢ²/(2mᵢ)`.

### Query: `solves Kinetic Equation iff`
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The adapter unfolds to the admitted Physlib Hamilton-equation operator.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.
- `ArchonPhysics.HarmonicModes.differenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The matrix of the periodic forward nearest-neighbour difference.

### Query: `kinetic Solution rescale`
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Rescaling the phase-space configuration factors out the positive energy scale.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.
- `ArchonPhysics.Lattice.kineticEnergy` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The finite kinetic energy `∑ᵢ pᵢ²/(2mᵢ)`.

### Query: `first State Hitting Time`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

### Query: `first State Hitting Time eq s Inf`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.
- `ArchonPhysics.HittingTime.firstHittingTime_mono` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Enlarging an event can only make its first hitting time earlier.

### Query: `first State Hitting Time rescale`
- `ArchonPhysics.HittingTime.firstHittingTime` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | The first strictly positive event time, with `⊤` for an empty event set.
- `ArchonPhysics.HittingTime.firstHittingTime_empty` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | An event that never holds has first hitting time `⊤`.
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` | module `ArchonPhysics.HittingTime` | package ArchonPhysics | Every strictly positive event time bounds the first hitting time from above.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)
- `ArchonPhysics.Lattice.kineticEnergy` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.satisfiesHamiltonEquations_iff` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.differenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.latticeHamiltonian_rescale` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.Lattice.kineticEnergy` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_mono` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_empty` (ArchonPhysics)
- `ArchonPhysics.HittingTime.firstHittingTime_le_of_mem` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.KineticRescaling.SolvesKineticEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
