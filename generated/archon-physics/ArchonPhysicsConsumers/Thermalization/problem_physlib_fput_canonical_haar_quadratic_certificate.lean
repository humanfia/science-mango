import ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate

/-!
# Consumer: constructed canonical Haar quadratic certificate

This consumer constructs the final model-specific certificate at positive
block time, uses its exact nonnegative-profile representation, and instantiates
the resulting local sup-norm Lipschitz estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalHaarQuadraticCertificate

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

noncomputable section

/-- The final certificate is constructed from the proved FPUT character
algebra; it is not supplied as an assumption. -/
def problem_canonicalHaarQuadraticKernelCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {T : Real} (hT : 0 < T) :
    CanonicalHaarQuadraticKernelCertificate m kappa beta T :=
  canonicalHaarQuadraticKernelCertificate m kappa beta hT

/-- The constructed kernel exactly represents the canonical collision on the
physical nonnegative cone. -/
theorem problem_canonicalHaarQuadraticKernelCertificate_represents
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {T : Real} (hT : 0 < T)
    (energy : PositiveEnergyProfile m)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    canonicalHaarEnergyCollision m kappa beta T energy =
      finiteQuadraticCollisionField
        (problem_canonicalHaarQuadraticKernelCertificate
          m kappa beta hT).kernel energy :=
  (problem_canonicalHaarQuadraticKernelCertificate
    m kappa beta hT).represents_nonnegative energy henergy

/-- The same constructed certificate supplies the explicit local Lipschitz
constant on a nonnegative sup-norm ball. -/
theorem problem_canonicalHaarQuadraticKernelCertificate_localLipschitz
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T R : Real)
    (hT : 0 < T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁ : ‖energy₁‖ ≤ R) (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass
        (problem_canonicalHaarQuadraticKernelCertificate
          m kappa beta hT).kernel) *
        ‖energy₁ - energy₂‖ :=
  norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    m kappa beta T R
    (problem_canonicalHaarQuadraticKernelCertificate m kappa beta hT)
    energy₁ energy₂ hR henergy₁Nonneg henergy₂Nonneg henergy₁ henergy₂

#print axioms canonicalHaarEnergyCollision_eq_quadraticPolynomial
#print axioms canonicalHaarQuadraticKernelCertificate
#print axioms problem_canonicalHaarQuadraticKernelCertificate
#print axioms problem_canonicalHaarQuadraticKernelCertificate_represents
#print axioms problem_canonicalHaarQuadraticKernelCertificate_localLipschitz

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalHaarQuadraticCertificate
