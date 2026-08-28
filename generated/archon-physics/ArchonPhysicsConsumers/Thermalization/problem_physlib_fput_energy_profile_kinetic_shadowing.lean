import ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

/-!
# Consumer: compatibility-free FPUT energy-profile kinetic shadowing

This consumer checks that the complete positive-mode collision is the
canonical Haar broadening by definition and that the finite-block shadowing
theorem has no scalar collision-compatibility argument.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

#check canonicalHaarEnergyCollision
#check canonicalHaarInitialMoment_eq_modeAction
#check canonicalHaarEnergyBlockInitial_eq
#check canonicalHaarEnergyBlock_is_profileKineticEulerResidual
#check FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actual_is_profileKineticEulerResidual
#check FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actual_energyProfile_kineticEuler_shadowing_uniform_bound
#check FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actual_energyProfile_kineticTime_shadowing_bound

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (energy : PositiveEnergyProfile m)
    (mode : PositiveFrequencyMode m) :
    canonicalHaarEnergyCollision m kappa beta T energy mode =
      modeFrequency m mode *
        PhyslibFPUTSecondOrderResolvedStrataCrossBound.normalizedSecondOrderHaarBroadening
          m kappa beta (extendPositiveEnergyProfile m energy) mode T := by
  rfl

#print axioms canonicalHaarInitialMoment_eq_modeAction
#print axioms canonicalHaarEnergyBlock_is_profileKineticEulerResidual
#print axioms FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actual_energyProfile_kineticEuler_shadowing_uniform_bound
#print axioms FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actual_energyProfile_kineticTime_shadowing_bound

end ArchonPhysicsConsumers.Thermalization
