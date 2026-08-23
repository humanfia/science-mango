# Physics LeanExplore Grounding Log

- Target Lean file: `ArchonPhysics/HarmonicModes.lean`
- Blueprint chapter: `blueprint/src/chapters/ArchonPhysics_HarmonicModes.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c371bc3c62c775eaf3b82c173985a5efed5e255c349ac736a18fc75eb591856e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | The characteristic length `ξ` of the harmonic oscillator is defined as `√(ℏ /(m ω))`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Real.sqrt square root`
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.Lattice.sqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the square root of the mass profile.
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | Pointwise multiplication of a configuration by the square root of the energy scale.

### Query: `derivative at a point`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `difference Matrix`
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.
- `ArchonPhysics.Lattice.forwardDifference_apply` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise expansion of the periodic forward difference.
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.

### Query: `difference Matrix mul Vec`
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling_inv_sq` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The inverse-square effective-coupling law; this is algebraic only.
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The coupling after extracting a positive energy scale.
- `ArchonPhysics.Lattice.forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The periodic forward nearest-neighbour difference.

### Query: `mass Weighted Difference Matrix`
- `ArchonPhysics.Lattice.sum_forwardDifference` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Forward differences telescope around a nonempty periodic chain.
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The mass at each periodic site.

### Query: `mass Weighted Harmonic Matrix`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The mass at each periodic site.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Every site has strictly positive mass.

### Query: `mass Weighted Harmonic Matrix eq transpose mul self`
- `ArchonPhysics.Lattice.inverseMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse mass profile.
- `ArchonPhysics.Lattice.inverseSqrtMassAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the inverse square root of the mass profile.
- `ArchonPhysics.Lattice.massAction` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Pointwise multiplication by the mass profile.

### Query: `mass Weighted Harmonic Matrix pos Semidef`
- `ArchonPhysics.Lattice.PositiveMassConfig` | module `ArchonPhysics.Lattice` | package ArchonPhysics | A deterministic, pointwise strictly positive mass realization.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The mass at each periodic site.
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Every site has strictly positive mass.

### Query: `modal Energy`
- `ArchonPhysics.Lattice.kineticEnergy` | module `ArchonPhysics.Lattice` | package ArchonPhysics | The finite kinetic energy `∑ᵢ pᵢ²/(2mᵢ)`.
- `ArchonPhysics.Lattice.kineticEnergy_nonneg` | module `ArchonPhysics.Lattice` | package ArchonPhysics | Kinetic energy is nonnegative for a pointwise strictly positive mass profile.
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` | module `ArchonPhysics.HamiltonianScaling` | package ArchonPhysics | The Physlib Hamilton-equation residual vanishes along the phase-space path.

## Grounded Mathlib/PhysLean names

- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.sqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.rescaleConfiguration` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mk` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference_apply` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling_inv_sq` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.effectiveCoupling` (ArchonPhysics)
- `ArchonPhysics.Lattice.forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.sum_forwardDifference` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.inverseSqrtMassAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.massAction` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass` (ArchonPhysics)
- `ArchonPhysics.Lattice.PositiveMassConfig.mass_pos` (ArchonPhysics)
- `ArchonPhysics.Lattice.kineticEnergy` (ArchonPhysics)
- `ArchonPhysics.Lattice.kineticEnergy_nonneg` (ArchonPhysics)
- `ArchonPhysics.HamiltonianScaling.SatisfiesHamiltonEquations` (ArchonPhysics)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
