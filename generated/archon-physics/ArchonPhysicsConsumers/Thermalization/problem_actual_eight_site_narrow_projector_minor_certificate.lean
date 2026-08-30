import ArchonPhysics.ActualEightSiteNarrowProjectorMinorCertificate

/-!
Consumer replay and trust audit for the uniform nonzero projector-minor
certificate on the narrow physical eight-site path.
-/

open Set

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorCertificate
open ArchonPhysics.FinEightAdjugateContractionPerturbation

noncomputable section

theorem problem_actualEightSite_narrow_shiftedAdjugate_reference_error
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r s : Fin 3) :
    |actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
      actualEightSiteNarrowRationalReferenceWeightMatrix r s| ≤
        (1 : Real) / 1000000 :=
  actualEightSiteNarrowShiftedAdjugateWeightMatrix_close_reference ht r s

theorem problem_actualEightSite_selectedProjectorMinor_ne_zero_on_narrow :
    ∀ t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper,
      actualEightSiteSelectedProjectorMinor
        (actualEightSiteRationalMassPath t) ≠ 0 :=
  actualEightSiteSelectedProjectorMinor_ne_zero_on_narrow

#print axioms reindexVector_actualEightSiteSelectedDirection
#print axioms actualEightSiteSelectedAdjugateEntry_close_center
#print axioms actualEightSiteNarrowWeight_close_center
#print axioms actualEightSiteCenterAdjugateWeightMatrix_close_reference
#print axioms actualEightSiteNarrowShiftedAdjugateWeightMatrix_close_reference
#print axioms actualEightSiteSelectedProjectorMinor_ne_zero_on_narrow
#print axioms problem_actualEightSite_narrow_shiftedAdjugate_reference_error
#print axioms problem_actualEightSite_selectedProjectorMinor_ne_zero_on_narrow

end

end ArchonPhysicsConsumers.Thermalization
