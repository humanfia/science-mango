import ArchonPhysics.CanonicalIIDCoerciveUnbalancedArbitraryOrderSubkineticRPA

/-!
# Thermalization consumer: arbitrary-order unbalanced subkinetic RPA

This consumer checks the unconditional fixed-order telescope closure in the
exact Haar-unbalanced sector.  Its time range is `|g| |t| -> 0`; it does not
assert kinetic-time factorization.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalIIDCoerciveUnbalancedArbitraryOrderSubkineticRPA

noncomputable section

theorem problem_canonical_iid_coercive_unbalanced_arbitrary_order_subkinetic_rpa :
    type_of%
      (@canonicalAnnealedUnbalancedHigherOrderRPA_tendsto_zero_at_subkineticTime) :=
  @canonicalAnnealedUnbalancedHigherOrderRPA_tendsto_zero_at_subkineticTime

#print axioms
  canonicalAnnealedUnbalancedHigherOrderRPA_tendsto_zero_at_subkineticTime
#print axioms
  problem_canonical_iid_coercive_unbalanced_arbitrary_order_subkinetic_rpa

end

end ArchonPhysicsConsumers.Thermalization
