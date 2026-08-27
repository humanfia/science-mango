import ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion

noncomputable section

theorem problem_cubicPhaseMismatch_eq_zero_of_charge_eq_freeInitial
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : CubicPhaseTerm N)
    (hcharge : cubicPhaseCharge term = freeInitialPhaseCharge observed 0) :
    cubicPhaseMismatch frequency observed term = 0 :=
  cubicPhaseMismatch_eq_zero_of_charge_eq_freeInitial
    frequency observed term hcharge

theorem problem_equalChargeFamilyInterference_freeInitial_directCubic_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta time : Real)
    (radius frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed)
        (oscillatoryCoefficient
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (frequency observed) beta)
            m observed radius)
          (cubicPhaseMismatch frequency observed) time)
        cubicPhaseCharge = 0 :=
  equalChargeFamilyInterference_freeInitial_directCubic_eq_zero
    m beta time radius frequency observed

#print axioms problem_cubicPhaseMismatch_eq_zero_of_charge_eq_freeInitial
#print axioms
  problem_equalChargeFamilyInterference_freeInitial_directCubic_eq_zero

end


end ArchonPhysicsConsumers.Thermalization
