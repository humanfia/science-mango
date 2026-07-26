# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0555.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0555.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6c739fb58f1d641301a0a802170e8a0fafbb35fcdfe9bd34bd4f9c82739d87af
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `energy In Mega Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `energy In Giga Electron Volts`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.

### Query: `Particle Species`
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `SMCharges.toSpecies_apply_eq` | module `Physlib.Particles.StandardModel.AnomalyCancellation.Basic` | package PhysLean | **Standard Model Charge Species Component.** For any index $i \in \{0, \dots, 4\}$ and any set of charges $S$ in the Standard Model with $n$ generations, the $i$-th species of charges in $S$ is equal to the function m...
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...

### Query: `Electric Charge Sign`
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `ChargeUnit` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The choices of translationally-invariant metrics on the charge-manifold. Such a choice corresponds to a choice of units for charge. This assumes that an orientation has already being picked on the charge manifold.

### Query: `charge Sign`
- `ChargeUnit` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The choices of translationally-invariant metrics on the charge-manifold. Such a choice corresponds to a choice of units for charge. This assumes that an orientation has already being picked on the charge manifold.
- `Real.sign` | module `Mathlib.Data.Real.Sign` | package Mathlib | The sign function that maps negative real numbers to -1, positive numbers to 1, and 0 otherwise.
- `ComplexShape.χ` | module `Mathlib.Algebra.Homology.EulerCharacteristic` | package Mathlib | The sign at index `i` for Euler characteristic computations.

### Query: `Reaction Particle`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.FreeParticle.velocity` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | The velocity of a trajectory at a given time. This is defined as the time derivative of the position function.

### Query: `species`
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `SMRHN.toSpecies_familyUniversal` | module `Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps` | package PhysLean | **Species Consistency of the Universal Family.** For any natural number $n$, any index $j \in \{0, \dots, 5\}$, any charge $S$ of type $\text{SM}\nu$, and any index $i \in \{0, \dots, n-1\}$, the $j$-th species of the...
- `TensorSpecies` | module `Physlib.Relativity.Tensors.TensorSpecies.Basic` | package PhysLean | The structure `TensorSpecies` contains the necessary structure needed to define a system of tensors with index notation. Examples of `TensorSpecies` include real Lorentz tensors, complex Lorentz tensors, and ordinary...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `TensorSpecies.Tensor` (PhysLean)
- `SMCharges.toSpecies_apply_eq` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `ChargeUnit` (PhysLean)
- `ChargeUnit` (PhysLean)
- `Real.sign` (Mathlib)
- `ComplexShape.χ` (Mathlib)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.FreeParticle.velocity` (PhysLean)
- `TensorSpecies.Tensor` (PhysLean)
- `SMRHN.toSpecies_familyUniversal` (PhysLean)
- `TensorSpecies` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0555.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.AntiprotonProductionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.ElectricChargeSign`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.FigureAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.FigureColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.FigurePanel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.FigureParticleGlyph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.FixedTargetAntiprotonSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.HasPhysicalAntiprotonProductionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.HorizontalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.MatchesDisplayedThresholdChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.MatchesFixedTargetThresholdScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.MatchesProblemRestEnergyData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.MatchesSuppliedAntiprotonFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.ParticleSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.ReactionParticle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.ReactionParticle.IsOutgoing`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0555.SatisfiesRelativisticThresholdLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
