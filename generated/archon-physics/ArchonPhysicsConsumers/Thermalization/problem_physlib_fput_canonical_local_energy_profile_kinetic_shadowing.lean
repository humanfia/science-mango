import ArchonPhysics.PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing

/-!
# Consumer: canonical orbit-local profile shadowing

This checks that the constructed canonical Haar quadratic kernel is inserted
internally into the local collision, residual, finite-block, and kinetic-time
theorems.  No abstract kernel certificate is a consumer argument.
-/

namespace ArchonPhysicsConsumers.Thermalization
namespace PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing
open LocalEnergyProfileKineticOrbitEnvelope
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing

noncomputable section

variable {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}
  {certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
    m kappa beta T g E Cref Ccoupling}
  {n : Nat} {V : Nat → PositiveEnergyProfile m} {R : Real}

theorem problem_canonical_local_collision_lipschitz
    (hT : 0 < T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁ : ‖energy₁‖ ≤ R) (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      canonicalLocalCollisionLipschitzConstant m kappa beta hT R *
        ‖energy₁ - energy₂‖ :=
  norm_canonicalHaarEnergyCollision_sub_le_on_nonnegativeBall
    m kappa beta hT energy₁ energy₂ R hR
      henergy₁Nonneg henergy₂Nonneg henergy₁ henergy₂

theorem problem_canonical_local_actual_residual
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (hT : 0 < T) (j : Nat) :
    EnergyProfileKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T (E n j))
      (certificate.actualResidualDefect
        (canonicalLocalCollisionLipschitzConstant m kappa beta hT R) n) :=
  canonical_actual_is_profileKineticEulerResidual envelope hT j

theorem problem_canonical_local_finite_block_shadowing
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
            (g n ^ 2 * T) * (K : Real)) :=
  canonical_actual_energyProfile_kineticEuler_shadowing_local_bound
    envelope hT hkinetic K

theorem problem_canonical_local_kinetic_time_shadowing
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
        Real.exp (L * tau) :=
  canonical_actual_energyProfile_kineticTime_local_bound
    envelope hT hkinetic K tau hkineticBudget

#print axioms problem_canonical_local_collision_lipschitz
#print axioms problem_canonical_local_actual_residual
#print axioms problem_canonical_local_finite_block_shadowing
#print axioms problem_canonical_local_kinetic_time_shadowing

end


end PhyslibFPUTCanonicalLocalEnergyProfileKineticShadowing
end ArchonPhysicsConsumers.Thermalization
