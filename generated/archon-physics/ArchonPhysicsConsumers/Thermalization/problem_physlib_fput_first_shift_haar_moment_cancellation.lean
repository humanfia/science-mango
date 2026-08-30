import ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation

/-!
# Consumer: first-shift Haar moment cancellation

This gate checks both the exact absence of a coupling-linear term in the
canonical Haar reference moment and the cubic actual/reference endpoint
discrepancy for the first physical Hamiltonian block.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFirstShiftHaarMomentCancellation

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion

noncomputable section

#check physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
#check abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube

/-- Consumer-level exact first-variation factorization. -/
theorem canonical_firstShift_quadraticMoment_has_no_linearTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (time : Real)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius time observed -
        physlibReferenceInitialHaarMoment m radius observed =
      g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
          m kappa beta radius time observed +
        g ^ 3 * equalChargeFamilyInterference
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge :=
  physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
    m kappa beta radius time observed g homega

#print axioms physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
#print axioms abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
#print axioms canonical_firstShift_quadraticMoment_has_no_linearTerm

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFirstShiftHaarMomentCancellation
