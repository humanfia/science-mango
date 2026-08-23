# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysicsConsumers/Thermalization/problem_mass_matrix.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_Generated_problem_mass_matrix.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6ccdc57dce30e737ef01472701b6e2ccafae2f08e45af06271ac0100514ded45
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.Lattice.sqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the square root of the mass profile.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.

### Query: `Positive masses`
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The unit-mass Physlib oscillator associated with a positive mode frequency.
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The oscillator adapter has unit mass and spring constant `omega²`.
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | A positive normal-mode oscillator conserves Physlib's energy along its equation of motion.

### Query: `Mass operator`
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.

### Query: `Inverse mass operator`
- `ArchonPhysics.Lattice.inverseMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse mass profile.
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.

### Query: `Kinetic form`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `Mass-weighted coordinate`
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.

### Query: `Inverse cancellation and kinetic nonnegativity`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.

### Query: `kinetic Quadratic Form`
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | A trajectory solves the effective kinetic equation with coupling `g`.
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling.
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` | module `ArchonPhysics.KineticRescaling` | package ArchonPhysics | The kinetic-solution predicate unfolds to its initial-value and derivative data.

### Query: `mass Weighted Coordinate`
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.

### Query: `mass matrix physics formalization target`
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The difference matrix after inverse-square-root mass weighting.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The symmetric positive-semidefinite mass-weighted harmonic matrix.
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` | module `ArchonPhysics.HarmonicModes` | package ArchonPhysics | The mass-weighted harmonic matrix is the Gram matrix of the weighted difference.

## Grounded Mathlib/PhysLean names

- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.sqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveModeOscillator_spec` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.positiveMode_energy_conserved` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.SolvesKineticEquation` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.kineticSolution_rescale` (ArchonPhysics)
- `ArchonPhysics.KineticRescaling.solvesKineticEquation_iff` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedDifferenceMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix` (ArchonPhysics)
- `ArchonPhysics.HarmonicModes.massWeightedHarmonicMatrix_eq_transpose_mul_self` (ArchonPhysics)

## Local abstractions introduced

- `ArchonPhysics.Generated.MassMatrix.PositiveMasses`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
