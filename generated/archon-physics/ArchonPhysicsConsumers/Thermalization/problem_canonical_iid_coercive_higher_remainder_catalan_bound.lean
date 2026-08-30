import ArchonPhysics.CanonicalIIDCoerciveHigherRemainderCatalanBound

/-!
# Consumer: Catalan control of the genuine higher-order remainder

This consumer checks the finite Picard-window estimate, the conditional
geometric tail closure, and the kinetic-time obstruction for a bare
one-coupling-per-vertex Duhamel estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveHigherRemainderCatalanBound

noncomputable section

/-- Consumer alias for the exact orderwise Catalan-capacity estimate. -/
theorem problem_norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated :
    type_of%
      (@norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated) :=
  @norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated

/-- Consumer alias for the unconditional finite Picard-window bound. -/
theorem problem_norm_fixedRootRawHistoryFiniteWindow_le_exactCapacity_sum :
    type_of%
      (@norm_fixedRootRawHistoryFiniteWindow_le_exactCapacity_sum) :=
  @norm_fixedRootRawHistoryFiniteWindow_le_exactCapacity_sum

/-- Consumer alias for the regular/repeated geometric tail closure. -/
theorem problem_norm_fixedRootRawHistoryTail_le_of_regular_repeated_catalanScale :
    type_of%
      (@norm_fixedRootRawHistoryTail_le_of_regular_repeated_catalanScale) :=
  @norm_fixedRootRawHistoryTail_le_of_regular_repeated_catalanScale

/-- Consumer alias for the minimal varying-envelope convergence criterion. -/
theorem problem_higherRemainder_tendsto_zero_of_varyingCatalanEnvelope :
    type_of% (@higherRemainder_tendsto_zero_of_varyingCatalanEnvelope) :=
  @higherRemainder_tendsto_zero_of_varyingCatalanEnvelope

/-- Consumer alias for the fixed-ratio, increasing-order closure. -/
theorem problem_higherRemainder_tendsto_zero_of_uniformCatalanRatio :
    type_of% (@higherRemainder_tendsto_zero_of_uniformCatalanRatio) :=
  @higherRemainder_tendsto_zero_of_uniformCatalanRatio

/-- Consumer alias for the sharp kinetic-time noncontractivity theorem. -/
theorem problem_not_eventually_linearCoupling_kineticCatalanRatio_lt_one :
    type_of% (@not_eventually_linearCoupling_kineticCatalanRatio_lt_one) :=
  @not_eventually_linearCoupling_kineticCatalanRatio_lt_one

#check fixedRootRawHistoryFiniteWindow
#check linearCoupling_kineticCatalanRatio_eq
#check linearCoupling_kineticCatalanRatio_lt_one_forces

#print axioms
  norm_fixedRootRawHistoryOrderSum_le_exactCapacity_regular_add_repeated
#print axioms norm_fixedRootRawHistoryFiniteWindow_le_exactCapacity_sum
#print axioms
  norm_fixedRootRawHistoryTail_le_of_regular_repeated_catalanScale
#print axioms higherRemainder_tendsto_zero_of_varyingCatalanEnvelope
#print axioms higherRemainder_tendsto_zero_of_uniformCatalanRatio
#print axioms not_eventually_linearCoupling_kineticCatalanRatio_lt_one
#print axioms
  problem_not_eventually_linearCoupling_kineticCatalanRatio_lt_one

end

end ArchonPhysicsConsumers.Thermalization
