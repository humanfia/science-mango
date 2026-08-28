import ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel

/-!
# Consumer: canonical quadratic kernel

This consumer checks the exact finite positive-mode expansion of one modal
action and of a product of two modal actions.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQuadraticKernel

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

noncomputable section

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) (site : Lattice.Site N) :
    modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) site =
      ∑ input : PositiveFrequencyMode m,
        extendedModeActionCoefficient m site input * energy input :=
  modeAction_extendPositiveEnergyProfile_eq_sum m energy site

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m)
    (first second : Lattice.Site N) :
    modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
        modeAction (extendPositiveEnergyProfile m energy)
          (modeFrequency m) second =
      ∑ i : PositiveFrequencyMode m, ∑ j : PositiveFrequencyMode m,
        extendedModeActionProductKernel m first second i j *
          energy i * energy j :=
  modeAction_mul_modeAction_eq_quadraticSum m energy first second

#print axioms modeAction_extendPositiveEnergyProfile_eq_sum
#print axioms modeAction_mul_modeAction_eq_quadraticSum

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQuadraticKernel
