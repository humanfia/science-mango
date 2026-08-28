import ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing

/-!
# Consumer: orbit-local energy-profile kinetic shadowing

This consumer checks that a quadratic-kernel certificate and transparent
nonnegative radius-`R` orbit envelopes replace the former global collision
Lipschitz hypothesis in the residual, finite-block, and kinetic-time bounds.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTLocalEnergyProfileKineticShadowing

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
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

def problem_local_energy_profile_lipschitz_constant
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T) : Real :=
  localCollisionLipschitzConstant kernelCertificate R

theorem problem_local_energy_profile_endpoint_collision
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (j : Nat) :
    ‖canonicalHaarEnergyCollision m kappa beta T
          (canonicalHaarEnergyBlockInitial m
            (certificate.referenceEnergy n j)) -
        canonicalHaarEnergyCollision m kappa beta T (E n j)‖ ≤
      localCollisionLipschitzConstant kernelCertificate R *
        ‖canonicalHaarEnergyBlockInitial m
            (certificate.referenceEnergy n j) - E n j‖ :=
  envelope.collision_reference_actual_le kernelCertificate j

theorem problem_local_energy_profile_orbit_collision
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (j : Nat) :
    ‖canonicalHaarEnergyCollision m kappa beta T (E n j) -
        canonicalHaarEnergyCollision m kappa beta T (V j)‖ ≤
      localCollisionLipschitzConstant kernelCertificate R *
        ‖E n j - V j‖ :=
  envelope.collision_actual_kinetic_le kernelCertificate j

theorem problem_local_energy_profile_actual_residual
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T) (j : Nat) :
    EnergyProfileKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T (E n j))
      (certificate.actualResidualDefect
        (localCollisionLipschitzConstant kernelCertificate R) n) :=
  envelope.actual_is_profileKineticEulerResidual_of_quadraticKernel
    kernelCertificate hT j

theorem problem_local_energy_profile_finite_block_shadowing
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) :
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (K : Real) * certificate.actualResidualDefect
            (localCollisionLipschitzConstant kernelCertificate R) n) *
        Real.exp
          (localCollisionLipschitzConstant kernelCertificate R *
            (g n ^ 2 * T) * (K : Real)) :=
  envelope.actual_energyProfile_kineticEuler_shadowing_local_bound
    kernelCertificate hT hkinetic K

theorem problem_local_energy_profile_kinetic_time_shadowing
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    let L := localCollisionLipschitzConstant kernelCertificate R
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (tau / T) * certificate.kineticCubicConstant L * |g n|) *
        Real.exp (L * tau) :=
  envelope.actual_energyProfile_kineticTime_local_bound
    kernelCertificate hT hkinetic K tau hkineticBudget

#print axioms problem_local_energy_profile_lipschitz_constant
#print axioms problem_local_energy_profile_endpoint_collision
#print axioms problem_local_energy_profile_orbit_collision
#print axioms problem_local_energy_profile_actual_residual
#print axioms problem_local_energy_profile_finite_block_shadowing
#print axioms problem_local_energy_profile_kinetic_time_shadowing

end


end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTLocalEnergyProfileKineticShadowing
