import ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate
import ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing

/-!
# Canonical orbit-local energy-profile kinetic shadowing

The canonical finite-time Haar energy collision now has a constructed
quadratic-kernel certificate at every positive block time.  This module plugs
that construction into the orbit-local profile estimates, so callers no
longer supply an abstract `CanonicalHaarQuadraticKernelCertificate`.

The remaining assumptions are unchanged and transparent: positive block time,
the nonnegative radius-`R` actual/kinetic/reference envelope, the blockwise
canonical-Haar endpoint/residual certificate, and the kinetic Euler trajectory.
No RPA, radius invariance, or kinetic trajectory existence statement is added.
-/

namespace ArchonPhysics.PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing

noncomputable section

/-- The local Lipschitz constant of the constructed canonical quadratic
kernel on the nonnegative radius-`R` profile ball. -/
def canonicalLocalCollisionLipschitzConstant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {T : Real} (hT : 0 < T) (R : Real) : Real :=
  localCollisionLipschitzConstant
    (canonicalHaarQuadraticKernelCertificate m kappa beta hT) R

theorem canonicalLocalCollisionLipschitzConstant_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {T R : Real} (hT : 0 < T) (hR : 0 ≤ R) :
    0 ≤ canonicalLocalCollisionLipschitzConstant m kappa beta hT R := by
  exact localCollisionLipschitzConstant_nonneg
    (canonicalHaarQuadraticKernelCertificate m kappa beta hT) hR

/-- Canonical local collision Lipschitz estimate with no representation
certificate argument. -/
theorem norm_canonicalHaarEnergyCollision_sub_le_on_nonnegativeBall
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {T : Real} (hT : 0 < T)
    (energy₁ energy₂ : PositiveEnergyProfile m) (R : Real)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁ : ‖energy₁‖ ≤ R) (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      canonicalLocalCollisionLipschitzConstant m kappa beta hT R *
        ‖energy₁ - energy₂‖ := by
  exact norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    m kappa beta T R
      (canonicalHaarQuadraticKernelCertificate m kappa beta hT)
      energy₁ energy₂ hR henergy₁Nonneg henergy₂Nonneg
      henergy₁ henergy₂

namespace LocalEnergyProfileKineticOrbitEnvelope

variable {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}
  {certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
    m kappa beta T g E Cref Ccoupling}
  {n : Nat} {V : Nat → PositiveEnergyProfile m} {R : Real}

/-- Endpoint residual transfer using the constructed canonical kernel. -/
theorem canonical_actual_is_profileKineticEulerResidual
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (hT : 0 < T) (j : Nat) :
    EnergyProfileKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T (E n j))
      (certificate.actualResidualDefect
        (canonicalLocalCollisionLipschitzConstant m kappa beta hT R) n) := by
  exact envelope.actual_is_profileKineticEulerResidual_of_quadraticKernel
    (canonicalHaarQuadraticKernelCertificate m kappa beta hT) hT j

/-- Finite-block orbit-local profile shadowing with the canonical kernel
constructed internally. -/
theorem canonical_actual_energyProfile_kineticEuler_shadowing_local_bound
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) :
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (K : Real) * certificate.actualResidualDefect
            (canonicalLocalCollisionLipschitzConstant
              m kappa beta hT R) n) *
        Real.exp
          (canonicalLocalCollisionLipschitzConstant m kappa beta hT R *
            (g n ^ 2 * T) * (K : Real)) := by
  exact envelope.actual_energyProfile_kineticEuler_shadowing_local_bound
    (canonicalHaarQuadraticKernelCertificate m kappa beta hT)
    hT hkinetic K

/-- Kinetic-time `O(|g|)` specialization with the canonical kernel constructed
internally.  The radius envelope and blockwise RPA/residual data remain
visible through `envelope` and `certificate`. -/
theorem canonical_actual_energyProfile_kineticTime_local_bound
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    let L := canonicalLocalCollisionLipschitzConstant m kappa beta hT R
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (tau / T) * certificate.kineticCubicConstant L * |g n|) *
        Real.exp (L * tau) := by
  exact envelope.actual_energyProfile_kineticTime_local_bound
    (canonicalHaarQuadraticKernelCertificate m kappa beta hT)
      hT hkinetic K tau hkineticBudget

end LocalEnergyProfileKineticOrbitEnvelope

end


end ArchonPhysics.PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing
