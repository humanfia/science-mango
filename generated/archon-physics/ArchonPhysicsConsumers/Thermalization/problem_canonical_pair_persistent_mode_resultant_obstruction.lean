import ArchonPhysics.CanonicalPairPersistentModeResultantObstruction
import ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalPairPersistentModeResultantObstruction
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction

/-- The existing four-site opposite-edge example is recovered directly from
the general persistent-mode obstruction.  Here the persistent vector and
eigenvalue are the concrete `alternatingPairVector` and `2`; no persistent-mode
hypothesis is left to the consumer. -/
theorem fourSiteOpposite_resultant_eq_zero_via_persistentMode :
    twoSitePositiveCharacteristicJacobianResultant
        unitMassFour (0 : ArchonPhysics.Lattice.Site 4)
          (2 : ArchonPhysics.Lattice.Site 4) = 0 := by
  exact positiveCharacteristicJacobianResultant_eq_zero_of_persistent_mode
    unitMassFour (0 : ArchonPhysics.Lattice.Site 4)
      (2 : ArchonPhysics.Lattice.Site 4) 2 alternatingPairVector
      alternatingPairVector_ne_zero (by norm_num)
      opposite_slice_mulVec_alternating

#print axioms weightedCycleLaplacian_charpoly_eval_zero
#print axioms reduced_charpoly_eval_eq_zero_of_persistent_mode
#print axioms positiveCharacteristic_eval_eq_zero_of_persistent_mode
#print axioms
  positiveCharacteristicVerticalPartial_eval_eq_zero_of_persistent_mode
#print axioms
  positiveCharacteristicJacobianResultant_eq_zero_of_persistent_mode
#print axioms fourSiteOpposite_resultant_eq_zero_via_persistentMode

end ArchonPhysicsConsumers.Thermalization
