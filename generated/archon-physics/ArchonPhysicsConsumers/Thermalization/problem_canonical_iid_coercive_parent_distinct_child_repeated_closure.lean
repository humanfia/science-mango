import ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure

/-!
# Consumer: parent-distinct child-repeated recollision closure

This consumer verifies the literal Picard-label partition, the kinetic-time
IPR estimate for the parent-distinct child-repeated sector, and the resulting
reduction of the repeated-history residual to a named higher-order remainder.
The vanishing IPR ceiling remains an explicit hypothesis.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure

noncomputable section

/-- Consumer alias for the exact finite Picard-label collision partition. -/
theorem problem_sum_positiveQuadraticPicardLabel_eq_four_collision_sectors :
    type_of% (@sum_positiveQuadraticPicardLabel_eq_four_collision_sectors) :=
  @sum_positiveQuadraticPicardLabel_eq_four_collision_sectors

/-- Consumer alias for the exact parent-distinct/all-equal refinement. -/
theorem problem_positiveQuadraticPicardSectorSum_childRepeated_eq :
    type_of% (@positiveQuadraticPicardSectorSum_childRepeated_eq) :=
  @positiveQuadraticPicardSectorSum_childRepeated_eq

/-- Consumer alias for the physical Hamiltonian first-layer specialization. -/
theorem problem_physicalFirstLayerCollisionSum_eq_four_collision_sectors :
    type_of% (@physicalFirstLayerCollisionSum_eq_four_collision_sectors) :=
  @physicalFirstLayerCollisionSum_eq_four_collision_sectors

/-- Consumer alias for the finite-volume parent-distinct IPR estimate. -/
theorem problem_positiveParentDistinctChildRepeated_div_volume_le_of_ipr :
    type_of%
      (@positiveParentDistinctChildRepeatedBroadenedInteractionWeight_div_volume_le_of_ipr) :=
  @positiveParentDistinctChildRepeatedBroadenedInteractionWeight_div_volume_le_of_ipr

/-- Consumer alias for cancellation of kinetic time by the physical coupling
square, leaving the transparent IPR ceiling. -/
theorem problem_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr :
    type_of%
      (@physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr) :=
  @physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr

/-- Consumer alias for canonical kinetic convergence under `rho n -> 0`. -/
theorem problem_canonical_parentDistinct_at_kineticTime_tendsto_zero_of_ipr :
    type_of%
      (@canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_tendsto_zero_of_ipr) :=
  @canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_tendsto_zero_of_ipr

/-- Consumer alias for the reduced residual theorem. -/
theorem problem_repeatedHistoryBudget_tendsto_zero_of_ipr_and_higherRemainder :
    type_of%
      (@repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_ipr_and_higherRemainder) :=
  @repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_ipr_and_higherRemainder

#check orderedModesOfQuadraticPicardLabel
#check isPositiveOrderedTriple_orderedModesOfQuadraticPicardLabel_iff
#check positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_height
#check canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr

#print axioms sum_positiveQuadraticPicardLabel_eq_four_collision_sectors
#print axioms physicalFirstLayerCollisionSum_eq_four_collision_sectors
#print axioms
  positiveParentDistinctChildRepeatedBroadenedInteractionWeight_div_volume_le_of_ipr
#print axioms physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_ipr
#print axioms
  canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_tendsto_zero_of_ipr
#print axioms
  repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_ipr_and_higherRemainder
#print axioms
  problem_repeatedHistoryBudget_tendsto_zero_of_ipr_and_higherRemainder

end

end ArchonPhysicsConsumers.Thermalization
