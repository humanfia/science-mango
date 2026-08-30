import ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound

/-!
# Consumer: explicit repeated-history kinetic bounds

This consumer checks three logically separate endpoints:

* literal finite-history cardinality and norm bounds;
* the exact Catalan/sign/momentum capacity of fixed-root raw FPUT histories;
* volume-uniform kinetic-time decay of the two parent--child sectors and the
  all-equal child-repeated sector.

The final theorem keeps the parent-distinct child-repeated/higher-recollision
comparison as a named residual hypothesis.  It therefore does not assume RPA,
Markovianity, or an unproved recollision decay estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveRepeatedHistoryKineticBound

noncomputable section

/-- Consumer alias for the exact fixed-order `N`/coupling/order history
capacity bound. -/
theorem problem_fixedRootRaw_recollisionSectorNormBudget_le_explicit :
    type_of% (@fixedRootRaw_recollisionSectorNormBudget_le_explicit) :=
  @fixedRootRaw_recollisionSectorNormBudget_le_explicit

/-- Consumer alias for the unconditional three-sector kinetic ceiling. -/
theorem problem_canonicalControlledRepeatedCollisionBudget_at_kineticTime_le :
    type_of% (@canonicalControlledRepeatedCollisionBudget_at_kineticTime_le) :=
  @canonicalControlledRepeatedCollisionBudget_at_kineticTime_le

/-- Consumer alias for uniform-in-volume convergence of the controlled
repeated collision sectors. -/
theorem problem_canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero :
    type_of%
      (@canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero) :=
  @canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero

/-- Consumer alias displaying the exact unresolved residual estimate. -/
theorem problem_repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual :
    type_of% (@repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual) :=
  @repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual

#check finiteHistorySectorNormBudget_eq_sum_filter
#check finiteHistorySectorNormBudget_le_card_mul
#check card_fixedRootRawHistorySector_le_capacity
#check clusterSectorNormBudget_le_occurrenceCount_mul
#check fixedRootRaw_sectorOccurrenceCount_le
#check fractionalCeiling_at_kineticTime

#print axioms fixedRootRaw_recollisionSectorNormBudget_le_explicit
#print axioms canonicalControlledRepeatedCollisionBudget_at_kineticTime_le
#print axioms
  canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero
#print axioms repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual
#print axioms
  problem_fixedRootRaw_recollisionSectorNormBudget_le_explicit
#print axioms
  problem_canonicalControlledRepeatedCollisionBudget_at_kineticTime_tendsto_zero
#print axioms
  problem_repeatedHistoryBudget_at_kineticTime_tendsto_zero_of_residual

end

end ArchonPhysicsConsumers.Thermalization
