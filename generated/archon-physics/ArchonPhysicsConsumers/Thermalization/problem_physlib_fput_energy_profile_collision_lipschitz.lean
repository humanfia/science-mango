import ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz

noncomputable section

example {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode)
    (energy₁ energy₂ : mode → Real) (R : Real)
    (hR : 0 ≤ R) (henergy₁ : ‖energy₁‖ ≤ R)
    (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖finiteQuadraticCollisionField kernel energy₁ -
        finiteQuadraticCollisionField kernel energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass kernel) *
        ‖energy₁ - energy₂‖ := by
  exact norm_finiteQuadraticCollisionField_sub_le
    kernel energy₁ energy₂ R hR henergy₁ henergy₂

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T R : Real)
    (certificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁ : ‖energy₁‖ ≤ R) (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass certificate.kernel) *
        ‖energy₁ - energy₂‖ := by
  exact norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    m kappa beta T R certificate energy₁ energy₂ hR
      henergy₁Nonneg henergy₂Nonneg henergy₁ henergy₂

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T R : Real)
    (certificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁Upper : ∀ mode, energy₁ mode ≤ R)
    (henergy₂Upper : ∀ mode, energy₂ mode ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass certificate.kernel) *
        ‖energy₁ - energy₂‖ := by
  exact norm_canonicalHaarEnergyCollision_sub_le_on_nonnegativeBox
    m kappa beta T R certificate energy₁ energy₂ hR
      henergy₁Nonneg henergy₂Nonneg henergy₁Upper henergy₂Upper

end

end ArchonPhysicsConsumers.Thermalization

#print axioms ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz.norm_finiteQuadraticCollisionField_sub_le
#print axioms ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz.norm_canonicalHaarEnergyCollision_sub_le_on_nonnegativeBox
